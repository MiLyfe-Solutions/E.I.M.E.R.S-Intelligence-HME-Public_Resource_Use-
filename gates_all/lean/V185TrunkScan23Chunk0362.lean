import V185TrunkScan23Chunk0361

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2141029 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 1, 3, 2]
def baseStart_2141029 : Nat := 118140960795 + 2141029 * 2 ^ 59
def prefixEnd_2141029 : Nat := 4983230072969 + 3 ^ 40 * 2141029 * 2
def baseEnd_2141029 : Nat := 1099376972215208947891093

theorem tailTrace_2141029 : CollatzResearch.WordTrace tailWord_2141029 prefixEnd_2141029 1099376972215208947891093 := by
  unfold tailWord_2141029
  simp only [CollatzResearch.WordTrace]
  refine ⟨78089742960425066486738141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52059828640283377657825427 78089742960425066486738141)
  ·
    refine ⟨29283653610159399932526803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78089742960425066486738141 29283653610159399932526803)
    ·
      refine ⟨43925480415239099898790205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29283653610159399932526803 43925480415239099898790205)
      ·
        refine ⟨16472055155714662462046327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43925480415239099898790205 16472055155714662462046327)
        ·
          refine ⟨24708082733571993693069491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16472055155714662462046327 24708082733571993693069491)
          ·
            refine ⟨37062124100357990539604237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24708082733571993693069491 37062124100357990539604237)
            ·
              refine ⟨13898296537634246452351589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37062124100357990539604237 13898296537634246452351589)
              ·
                refine ⟨2605930600806421209815923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13898296537634246452351589 2605930600806421209815923)
                ·
                  refine ⟨3908895901209631814723885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2605930600806421209815923 3908895901209631814723885)
                  ·
                    refine ⟨1465835962953611930521457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3908895901209631814723885 1465835962953611930521457)
                    ·
                      refine ⟨1099376972215208947891093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465835962953611930521457 1099376972215208947891093)
                      ·
                        rfl

theorem cell23_2141029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_2141029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141029 prefixEnd_2141029 := by exact prefixLift 2141029
  have htrace : WordTrace (prefixWord ++ tailWord_2141029) baseStart_2141029 baseEnd_2141029 := by
    simpa [prefixWord, tailWord_2141029, baseEnd_2141029] using wordTrace_append hprefix tailTrace_2141029
  have hstable : (prefixWord ++ tailWord_2141029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141029).length < 2 ^ (prefixWord ++ tailWord_2141029).sum := by decide
  have hdescent : baseEnd_2141029 < baseStart_2141029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141055 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_2141055 : Nat := 118140960795 + 2141055 * 2 ^ 59
def prefixEnd_2141055 : Nat := 4983230072969 + 3 ^ 40 * 2141055 * 2
def baseEnd_2141055 : Nat := 1099390322712225846165973

theorem tailTrace_2141055 : CollatzResearch.WordTrace tailWord_2141055 prefixEnd_2141055 1099390322712225846165973 := by
  unfold tailWord_2141055
  simp only [CollatzResearch.WordTrace]
  refine ⟨78090691258330872927184619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52060460838887248618123079 78090691258330872927184619)
  ·
    refine ⟨117136036887496309390776929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78090691258330872927184619 117136036887496309390776929)
    ·
      refine ⟨87852027665622232043082697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117136036887496309390776929 87852027665622232043082697)
      ·
        refine ⟨65889020749216674032312023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87852027665622232043082697 65889020749216674032312023)
        ·
          refine ⟨98833531123825011048468035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65889020749216674032312023 98833531123825011048468035)
          ·
            refine ⟨148250296685737516572702053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98833531123825011048468035 148250296685737516572702053)
            ·
              refine ⟨27796930628575784357381635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148250296685737516572702053 27796930628575784357381635)
              ·
                refine ⟨41695395942863676536072453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27796930628575784357381635 41695395942863676536072453)
                ·
                  refine ⟨7817886739286939350513585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41695395942863676536072453 7817886739286939350513585)
                  ·
                    refine ⟨5863415054465204512885189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7817886739286939350513585 5863415054465204512885189)
                    ·
                      refine ⟨1099390322712225846165973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5863415054465204512885189 1099390322712225846165973)
                      ·
                        rfl

theorem cell23_2141055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_2141055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141055 prefixEnd_2141055 := by exact prefixLift 2141055
  have htrace : WordTrace (prefixWord ++ tailWord_2141055) baseStart_2141055 baseEnd_2141055 := by
    simpa [prefixWord, tailWord_2141055, baseEnd_2141055] using wordTrace_append hprefix tailTrace_2141055
  have hstable : (prefixWord ++ tailWord_2141055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141055).length < 2 ^ (prefixWord ++ tailWord_2141055).sum := by decide
  have hdescent : baseEnd_2141055 < baseStart_2141055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141059 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 4, 2, 2]
def baseStart_2141059 : Nat := 118140960795 + 2141059 * 2 ^ 59
def prefixEnd_2141059 : Nat := 4983230072969 + 3 ^ 40 * 2141059 * 2
def baseEnd_2141059 : Nat := 1099392376634843830515955

theorem tailTrace_2141059 : CollatzResearch.WordTrace tailWord_2141059 prefixEnd_2141059 1099392376634843830515955 := by
  unfold tailWord_2141059
  simp only [CollatzResearch.WordTrace]
  refine ⟨78090837150316381610330231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52060558100210921073553487 78090837150316381610330231)
  ·
    refine ⟨117136255725474572415495347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78090837150316381610330231 117136255725474572415495347)
    ·
      refine ⟨175704383588211858623243021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117136255725474572415495347 175704383588211858623243021)
      ·
        refine ⟨65889143845579446983716133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175704383588211858623243021 65889143845579446983716133)
        ·
          refine ⟨12354214471046146309446775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65889143845579446983716133 12354214471046146309446775)
          ·
            refine ⟨18531321706569219464170163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12354214471046146309446775 18531321706569219464170163)
            ·
              refine ⟨27796982559853829196255245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18531321706569219464170163 27796982559853829196255245)
              ·
                refine ⟨10423868459945185948595717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27796982559853829196255245 10423868459945185948595717)
                ·
                  refine ⟨1954475336239722365361697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10423868459945185948595717 1954475336239722365361697)
                  ·
                    refine ⟨1465856502179791774021273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1954475336239722365361697 1465856502179791774021273)
                    ·
                      refine ⟨1099392376634843830515955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465856502179791774021273 1099392376634843830515955)
                      ·
                        rfl

theorem cell23_2141059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_2141059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141059 prefixEnd_2141059 := by exact prefixLift 2141059
  have htrace : WordTrace (prefixWord ++ tailWord_2141059) baseStart_2141059 baseEnd_2141059 := by
    simpa [prefixWord, tailWord_2141059, baseEnd_2141059] using wordTrace_append hprefix tailTrace_2141059
  have hstable : (prefixWord ++ tailWord_2141059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141059).length < 2 ^ (prefixWord ++ tailWord_2141059).sum := by decide
  have hdescent : baseEnd_2141059 < baseStart_2141059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141112 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 2, 5]
def baseStart_2141112 : Nat := 118140960795 + 2141112 * 2 ^ 59
def prefixEnd_2141112 : Nat := 4983230072969 + 3 ^ 40 * 2141112 * 2
def baseEnd_2141112 : Nat := 366473197036510707717737

theorem tailTrace_2141112 : CollatzResearch.WordTrace tailWord_2141112 prefixEnd_2141112 366473197036510707717737 := by
  unfold tailWord_2141112
  simp only [CollatzResearch.WordTrace]
  refine ⟨39046385109562185831004795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52061846812749581108006393 39046385109562185831004795)
  ·
    refine ⟨58569577664343278746507193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39046385109562185831004795 58569577664343278746507193)
    ·
      refine ⟨43927183248257459059880395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58569577664343278746507193 43927183248257459059880395)
      ·
        refine ⟨65890774872386188589820593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43927183248257459059880395 65890774872386188589820593)
        ·
          refine ⟨49418081154289641442365445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65890774872386188589820593 49418081154289641442365445)
          ·
            refine ⟨9265890216429307770443521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49418081154289641442365445 9265890216429307770443521)
            ·
              refine ⟨6949417662321980827832641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9265890216429307770443521 6949417662321980827832641)
              ·
                refine ⟨5212063246741485620874481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6949417662321980827832641 5212063246741485620874481)
                ·
                  refine ⟨3909047435056114215655861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5212063246741485620874481 3909047435056114215655861)
                  ·
                    refine ⟨366473197036510707717737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3909047435056114215655861 366473197036510707717737)
                    ·
                      rfl

theorem cell23_2141112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_2141112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141112 prefixEnd_2141112 := by exact prefixLift 2141112
  have htrace : WordTrace (prefixWord ++ tailWord_2141112) baseStart_2141112 baseEnd_2141112 := by
    simpa [prefixWord, tailWord_2141112, baseEnd_2141112] using wordTrace_append hprefix tailTrace_2141112
  have hstable : (prefixWord ++ tailWord_2141112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141112).length < 2 ^ (prefixWord ++ tailWord_2141112).sum := by decide
  have hdescent : baseEnd_2141112 < baseStart_2141112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141132 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_2141132 : Nat := 118140960795 + 2141132 * 2 ^ 59
def prefixEnd_2141132 : Nat := 4983230072969 + 3 ^ 40 * 2141132 * 2
def baseEnd_2141132 : Nat := 1099429860722622044903119

theorem tailTrace_2141132 : CollatzResearch.WordTrace tailWord_2141132 prefixEnd_2141132 1099429860722622044903119 := by
  unfold tailWord_2141132
  simp only [CollatzResearch.WordTrace]
  refine ⟨39046749839525957538868825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52062333119367943385158433 39046749839525957538868825)
  ·
    refine ⟨29285062379644468154151619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39046749839525957538868825 29285062379644468154151619)
    ·
      refine ⟨43927593569466702231227429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29285062379644468154151619 43927593569466702231227429)
      ·
        refine ⟨8236423794275006668355143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43927593569466702231227429 8236423794275006668355143)
        ·
          refine ⟨12354635691412510002532715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8236423794275006668355143 12354635691412510002532715)
          ·
            refine ⟨18531953537118765003799073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12354635691412510002532715 18531953537118765003799073)
            ·
              refine ⟨13898965152839073752849305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18531953537118765003799073 13898965152839073752849305)
              ·
                refine ⟨10424223864629305314636979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13898965152839073752849305 10424223864629305314636979)
                ·
                  refine ⟨15636335796943957971955469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10424223864629305314636979 15636335796943957971955469)
                  ·
                    refine ⟨5863625923853984239483301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15636335796943957971955469 5863625923853984239483301)
                    ·
                      refine ⟨1099429860722622044903119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5863625923853984239483301 1099429860722622044903119)
                      ·
                        rfl

theorem cell23_2141132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_2141132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141132 prefixEnd_2141132 := by exact prefixLift 2141132
  have htrace : WordTrace (prefixWord ++ tailWord_2141132) baseStart_2141132 baseEnd_2141132 := by
    simpa [prefixWord, tailWord_2141132, baseEnd_2141132] using wordTrace_append hprefix tailTrace_2141132
  have hstable : (prefixWord ++ tailWord_2141132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141132).length < 2 ^ (prefixWord ++ tailWord_2141132).sum := by decide
  have hdescent : baseEnd_2141132 < baseStart_2141132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141133 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2141133 : Nat := 118140960795 + 2141133 * 2 ^ 59
def prefixEnd_2141133 : Nat := 4983230072969 + 3 ^ 40 * 2141133 * 2
def baseEnd_2141133 : Nat := 122158930467030726776735

theorem tailTrace_2141133 : CollatzResearch.WordTrace tailWord_2141133 prefixEnd_2141133 122158930467030726776735 := by
  unfold tailWord_2141133
  simp only [CollatzResearch.WordTrace]
  refine ⟨78093536152048292248524053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52062357434698861499016035 78093536152048292248524053)
  ·
    refine ⟨3660634507127263699149565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78093536152048292248524053 3660634507127263699149565)
    ·
      refine ⟨1372737940172723887181087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3660634507127263699149565 1372737940172723887181087)
      ·
        refine ⟨2059106910259085830771631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372737940172723887181087 2059106910259085830771631)
        ·
          refine ⟨3088660365388628746157447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059106910259085830771631 3088660365388628746157447)
          ·
            refine ⟨4632990548082943119236171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088660365388628746157447 4632990548082943119236171)
            ·
              refine ⟨6949485822124414678854257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4632990548082943119236171 6949485822124414678854257)
              ·
                refine ⟨5212114366593311009140693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6949485822124414678854257 5212114366593311009140693)
                ·
                  refine ⟨122158930467030726776735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5212114366593311009140693 122158930467030726776735)
                  ·
                    rfl

theorem cell23_2141133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2141133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141133 prefixEnd_2141133 := by exact prefixLift 2141133
  have htrace : WordTrace (prefixWord ++ tailWord_2141133) baseStart_2141133 baseEnd_2141133 := by
    simpa [prefixWord, tailWord_2141133, baseEnd_2141133] using wordTrace_append hprefix tailTrace_2141133
  have hstable : (prefixWord ++ tailWord_2141133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141133).length < 2 ^ (prefixWord ++ tailWord_2141133).sum := by decide
  have hdescent : baseEnd_2141133 < baseStart_2141133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141149 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2141149 : Nat := 118140960795 + 2141149 * 2 ^ 59
def prefixEnd_2141149 : Nat := 4983230072969 + 3 ^ 40 * 2141149 * 2
def baseEnd_2141149 : Nat := 1099438589893748478390541

theorem tailTrace_2141149 : CollatzResearch.WordTrace tailWord_2141149 prefixEnd_2141149 1099438589893748478390541 := by
  unfold tailWord_2141149
  simp only [CollatzResearch.WordTrace]
  refine ⟨78094119719990326981106501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52062746479993551320737667 78094119719990326981106501)
  ·
    refine ⟨14642647447498186308957469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78094119719990326981106501 14642647447498186308957469)
    ·
      refine ⟨5490992792811819865859051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14642647447498186308957469 5490992792811819865859051)
      ·
        refine ⟨8236489189217729798788577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5490992792811819865859051 8236489189217729798788577)
        ·
          refine ⟨6177366891913297349091433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8236489189217729798788577 6177366891913297349091433)
          ·
            refine ⟨4633025168934973011818575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6177366891913297349091433 4633025168934973011818575)
            ·
              refine ⟨6949537753402459517727863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4633025168934973011818575 6949537753402459517727863)
              ·
                refine ⟨10424306630103689276591795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949537753402459517727863 10424306630103689276591795)
                ·
                  refine ⟨15636459945155533914887693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10424306630103689276591795 15636459945155533914887693)
                  ·
                    refine ⟨5863672479433325218082885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15636459945155533914887693 5863672479433325218082885)
                    ·
                      refine ⟨1099438589893748478390541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5863672479433325218082885 1099438589893748478390541)
                      ·
                        rfl

theorem cell23_2141149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2141149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141149 prefixEnd_2141149 := by exact prefixLift 2141149
  have htrace : WordTrace (prefixWord ++ tailWord_2141149) baseStart_2141149 baseEnd_2141149 := by
    simpa [prefixWord, tailWord_2141149, baseEnd_2141149] using wordTrace_append hprefix tailTrace_2141149
  have hstable : (prefixWord ++ tailWord_2141149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141149).length < 2 ^ (prefixWord ++ tailWord_2141149).sum := by decide
  have hdescent : baseEnd_2141149 < baseStart_2141149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141162 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2141162 : Nat := 118140960795 + 2141162 * 2 ^ 59
def prefixEnd_2141162 : Nat := 4983230072969 + 3 ^ 40 * 2141162 * 2
def baseEnd_2141162 : Nat := 1099445265142256927527981

theorem tailTrace_2141162 : CollatzResearch.WordTrace tailWord_2141162 prefixEnd_2141162 1099445265142256927527981 := by
  unfold tailWord_2141162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19523648467235807550332435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52063062579295486800886493 19523648467235807550332435)
  ·
    refine ⟨29285472700853711325498653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19523648467235807550332435 29285472700853711325498653)
    ·
      refine ⟨10982052262820141747061995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29285472700853711325498653 10982052262820141747061995)
      ·
        refine ⟨16473078394230212620592993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10982052262820141747061995 16473078394230212620592993)
        ·
          refine ⟨12354808795672659465444745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16473078394230212620592993 12354808795672659465444745)
          ·
            refine ⟨9266106596754494599083559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12354808795672659465444745 9266106596754494599083559)
            ·
              refine ⟨13899159895131741898625339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9266106596754494599083559 13899159895131741898625339)
              ·
                refine ⟨20848739842697612847938009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13899159895131741898625339 20848739842697612847938009)
                ·
                  refine ⟨15636554882023209635953507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20848739842697612847938009 15636554882023209635953507)
                  ·
                    refine ⟨23454832323034814453930261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15636554882023209635953507 23454832323034814453930261)
                    ·
                      refine ⟨1099445265142256927527981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23454832323034814453930261 1099445265142256927527981)
                      ·
                        rfl

theorem cell23_2141162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2141162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141162 prefixEnd_2141162 := by exact prefixLift 2141162
  have htrace : WordTrace (prefixWord ++ tailWord_2141162) baseStart_2141162 baseEnd_2141162 := by
    simpa [prefixWord, tailWord_2141162, baseEnd_2141162] using wordTrace_append hprefix tailTrace_2141162
  have hstable : (prefixWord ++ tailWord_2141162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141162).length < 2 ^ (prefixWord ++ tailWord_2141162).sum := by decide
  have hdescent : baseEnd_2141162 < baseStart_2141162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141189 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 6]
def baseStart_2141189 : Nat := 118140960795 + 2141189 * 2 ^ 59
def prefixEnd_2141189 : Nat := 4983230072969 + 3 ^ 40 * 2141189 * 2
def baseEnd_2141189 : Nat := 122162125457769813543373

theorem tailTrace_2141189 : CollatzResearch.WordTrace tailWord_2141189 prefixEnd_2141189 122162125457769813543373 := by
  unfold tailWord_2141189
  simp only [CollatzResearch.WordTrace]
  refine ⟨78095578639845413812562621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52063719093230275875041747 78095578639845413812562621)
  ·
    refine ⟨29285841989942030179710983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78095578639845413812562621 29285841989942030179710983)
    ·
      refine ⟨43928762984913045269566475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29285841989942030179710983 43928762984913045269566475)
      ·
        refine ⟨65893144477369567904349713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43928762984913045269566475 65893144477369567904349713)
        ·
          refine ⟨49419858358027175928262285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65893144477369567904349713 49419858358027175928262285)
          ·
            refine ⟨18532446884260190973098357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49419858358027175928262285 18532446884260190973098357)
            ·
              refine ⟨1737416895399392903727971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18532446884260190973098357 1737416895399392903727971)
              ·
                refine ⟨2606125343099089355591957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737416895399392903727971 2606125343099089355591957)
                ·
                  refine ⟨122162125457769813543373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2606125343099089355591957 122162125457769813543373)
                  ·
                    rfl

theorem cell23_2141189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_2141189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141189 prefixEnd_2141189 := by exact prefixLift 2141189
  have htrace : WordTrace (prefixWord ++ tailWord_2141189) baseStart_2141189 baseEnd_2141189 := by
    simpa [prefixWord, tailWord_2141189, baseEnd_2141189] using wordTrace_append hprefix tailTrace_2141189
  have hstable : (prefixWord ++ tailWord_2141189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141189).length < 2 ^ (prefixWord ++ tailWord_2141189).sum := by decide
  have hdescent : baseEnd_2141189 < baseStart_2141189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141209 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 1, 5, 2]
def baseStart_2141209 : Nat := 118140960795 + 2141209 * 2 ^ 59
def prefixEnd_2141209 : Nat := 4983230072969 + 3 ^ 40 * 2141209 * 2
def baseEnd_2141209 : Nat := 1099469398733018243640265

theorem tailTrace_2141209 : CollatzResearch.WordTrace tailWord_2141209 prefixEnd_2141209 1099469398733018243640265 := by
  unfold tailWord_2141209
  simp only [CollatzResearch.WordTrace]
  refine ⟨78096308099772957228290681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52064205399848638152193787 78096308099772957228290681)
  ·
    refine ⟨58572231074829717921218011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78096308099772957228290681 58572231074829717921218011)
    ·
      refine ⟨87858346612244576881827017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58572231074829717921218011 87858346612244576881827017)
      ·
        refine ⟨65893759959183432661370263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87858346612244576881827017 65893759959183432661370263)
        ·
          refine ⟨98840639938775148992055395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65893759959183432661370263 98840639938775148992055395)
          ·
            refine ⟨148260959908162723488083093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98840639938775148992055395 148260959908162723488083093)
            ·
              refine ⟨6949732495695127663503895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 148260959908162723488083093 6949732495695127663503895)
              ·
                refine ⟨10424598743542691495255843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6949732495695127663503895 10424598743542691495255843)
                ·
                  refine ⟨15636898115314037242883765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10424598743542691495255843 15636898115314037242883765)
                  ·
                    refine ⟨1465959198310690991520353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15636898115314037242883765 1465959198310690991520353)
                    ·
                      refine ⟨1099469398733018243640265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465959198310690991520353 1099469398733018243640265)
                      ·
                        rfl

theorem cell23_2141209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_2141209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141209 prefixEnd_2141209 := by exact prefixLift 2141209
  have htrace : WordTrace (prefixWord ++ tailWord_2141209) baseStart_2141209 baseEnd_2141209 := by
    simpa [prefixWord, tailWord_2141209, baseEnd_2141209] using wordTrace_append hprefix tailTrace_2141209
  have hstable : (prefixWord ++ tailWord_2141209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141209).length < 2 ^ (prefixWord ++ tailWord_2141209).sum := by decide
  have hdescent : baseEnd_2141209 < baseStart_2141209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141219 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 1, 5]
def baseStart_2141219 : Nat := 118140960795 + 2141219 * 2 ^ 59
def prefixEnd_2141219 : Nat := 4983230072969 + 3 ^ 40 * 2141219 * 2
def baseEnd_2141219 : Nat := 366491511179854401505073

theorem tailTrace_2141219 : CollatzResearch.WordTrace tailWord_2141219 prefixEnd_2141219 366491511179854401505073 := by
  unfold tailWord_2141219
  simp only [CollatzResearch.WordTrace]
  refine ⟨78096672829736728936154711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52064448553157819290769807 78096672829736728936154711)
  ·
    refine ⟨117145009244605093404232067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78096672829736728936154711 117145009244605093404232067)
    ·
      refine ⟨175717513866907640106348101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117145009244605093404232067 175717513866907640106348101)
      ·
        refine ⟨32947033850045182519940269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 175717513866907640106348101 32947033850045182519940269)
        ·
          refine ⟨12355137693766943444977601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32947033850045182519940269 12355137693766943444977601)
          ·
            refine ⟨9266353270325207583733201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12355137693766943444977601 9266353270325207583733201)
            ·
              refine ⟨6949764952743905687799901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9266353270325207583733201 6949764952743905687799901)
              ·
                refine ⟨2606161857278964632924963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6949764952743905687799901 2606161857278964632924963)
                ·
                  refine ⟨3909242785918446949387445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606161857278964632924963 3909242785918446949387445)
                  ·
                    refine ⟨366491511179854401505073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3909242785918446949387445 366491511179854401505073)
                    ·
                      rfl

theorem cell23_2141219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 5].length) (baseStart_2141219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141219 prefixEnd_2141219 := by exact prefixLift 2141219
  have htrace : WordTrace (prefixWord ++ tailWord_2141219) baseStart_2141219 baseEnd_2141219 := by
    simpa [prefixWord, tailWord_2141219, baseEnd_2141219] using wordTrace_append hprefix tailTrace_2141219
  have hstable : (prefixWord ++ tailWord_2141219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141219).length < 2 ^ (prefixWord ++ tailWord_2141219).sum := by decide
  have hdescent : baseEnd_2141219 < baseStart_2141219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141256 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_2141256 : Nat := 118140960795 + 2141256 * 2 ^ 59
def prefixEnd_2141256 : Nat := 4983230072969 + 3 ^ 40 * 2141256 * 2
def baseEnd_2141256 : Nat := 1099493532323779559752549

theorem tailTrace_2141256 : CollatzResearch.WordTrace tailWord_2141256 prefixEnd_2141256 1099493532323779559752549 := by
  unfold tailWord_2141256
  simp only [CollatzResearch.WordTrace]
  refine ⟨39049011165301342127625811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52065348220401789503501081 39049011165301342127625811)
  ·
    refine ⟨58573516747952013191438717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39049011165301342127625811 58573516747952013191438717)
    ·
      refine ⟨21965068780482004946789519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58573516747952013191438717 21965068780482004946789519)
      ·
        refine ⟨32947603170723007420184279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21965068780482004946789519 32947603170723007420184279)
        ·
          refine ⟨49421404756084511130276419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32947603170723007420184279 49421404756084511130276419)
          ·
            refine ⟨74132107134126766695414629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49421404756084511130276419 74132107134126766695414629)
            ·
              refine ⟨13899770087648768755390243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74132107134126766695414629 13899770087648768755390243)
              ·
                refine ⟨20849655131473153133085365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13899770087648768755390243 20849655131473153133085365)
                ·
                  refine ⟨1954655168575608106226753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20849655131473153133085365 1954655168575608106226753)
                  ·
                    refine ⟨1465991376431706079670065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1954655168575608106226753 1465991376431706079670065)
                    ·
                      refine ⟨1099493532323779559752549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1465991376431706079670065 1099493532323779559752549)
                      ·
                        rfl

theorem cell23_2141256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_2141256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141256 prefixEnd_2141256 := by exact prefixLift 2141256
  have htrace : WordTrace (prefixWord ++ tailWord_2141256) baseStart_2141256 baseEnd_2141256 := by
    simpa [prefixWord, tailWord_2141256, baseEnd_2141256] using wordTrace_append hprefix tailTrace_2141256
  have hstable : (prefixWord ++ tailWord_2141256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141256).length < 2 ^ (prefixWord ++ tailWord_2141256).sum := by decide
  have hdescent : baseEnd_2141256 < baseStart_2141256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141262 : List Nat := [4, 1, 1, 1, 1, 3, 1, 11]
def baseStart_2141262 : Nat := 118140960795 + 2141262 * 2 ^ 59
def prefixEnd_2141262 : Nat := 4983230072969 + 3 ^ 40 * 2141262 * 2
def baseEnd_2141262 : Nat := 40722096785470612454723

theorem tailTrace_2141262 : CollatzResearch.WordTrace tailWord_2141262 prefixEnd_2141262 40722096785470612454723 := by
  unfold tailWord_2141262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762280146072618409996255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52065494112387298186646693 9762280146072618409996255)
  ·
    refine ⟨14643420219108927614994383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9762280146072618409996255 14643420219108927614994383)
    ·
      refine ⟨21965130328663391422491575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14643420219108927614994383 21965130328663391422491575)
      ·
        refine ⟨32947695492995087133737363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21965130328663391422491575 32947695492995087133737363)
        ·
          refine ⟨49421543239492630700606045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32947695492995087133737363 49421543239492630700606045)
          ·
            refine ⟨18533078714809736512727267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49421543239492630700606045 18533078714809736512727267)
            ·
              refine ⟨27799618072214604769090901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18533078714809736512727267 27799618072214604769090901)
              ·
                refine ⟨40722096785470612454723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 27799618072214604769090901 40722096785470612454723)
                ·
                  rfl

theorem cell23_2141262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_2141262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141262 prefixEnd_2141262 := by exact prefixLift 2141262
  have htrace : WordTrace (prefixWord ++ tailWord_2141262) baseStart_2141262 baseEnd_2141262 := by
    simpa [prefixWord, tailWord_2141262, baseEnd_2141262] using wordTrace_append hprefix tailTrace_2141262
  have hstable : (prefixWord ++ tailWord_2141262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141262).length < 2 ^ (prefixWord ++ tailWord_2141262).sum := by decide
  have hdescent : baseEnd_2141262 < baseStart_2141262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141269 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2141269 : Nat := 118140960795 + 2141269 * 2 ^ 59
def prefixEnd_2141269 : Nat := 4983230072969 + 3 ^ 40 * 2141269 * 2
def baseEnd_2141269 : Nat := 1099500207572288008889989

theorem tailTrace_2141269 : CollatzResearch.WordTrace tailWord_2141269 prefixEnd_2141269 1099500207572288008889989 := by
  unfold tailWord_2141269
  simp only [CollatzResearch.WordTrace]
  refine ⟨78098496479555587475474861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52065664319703724983649907 78098496479555587475474861)
  ·
    refine ⟨29286936179833345303303073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78098496479555587475474861 29286936179833345303303073)
    ·
      refine ⟨21965202134875008977477305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29286936179833345303303073 21965202134875008977477305)
      ·
        refine ⟨16473901601156256733107979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21965202134875008977477305 16473901601156256733107979)
        ·
          refine ⟨24710852401734385099661969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16473901601156256733107979 24710852401734385099661969)
          ·
            refine ⟨18533139301300788824746477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24710852401734385099661969 18533139301300788824746477)
            ·
              refine ⟨6949927237987795809279929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18533139301300788824746477 6949927237987795809279929)
              ·
                refine ⟨5212445428490846856959947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6949927237987795809279929 5212445428490846856959947)
                ·
                  refine ⟨7818668142736270285439921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5212445428490846856959947 7818668142736270285439921)
                  ·
                    refine ⟨5864001107052202714079941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7818668142736270285439921 5864001107052202714079941)
                    ·
                      refine ⟨1099500207572288008889989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5864001107052202714079941 1099500207572288008889989)
                      ·
                        rfl

theorem cell23_2141269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2141269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141269 prefixEnd_2141269 := by exact prefixLift 2141269
  have htrace : WordTrace (prefixWord ++ tailWord_2141269) baseStart_2141269 baseEnd_2141269 := by
    simpa [prefixWord, tailWord_2141269, baseEnd_2141269] using wordTrace_append hprefix tailTrace_2141269
  have hstable : (prefixWord ++ tailWord_2141269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141269).length < 2 ^ (prefixWord ++ tailWord_2141269).sum := by decide
  have hdescent : baseEnd_2141269 < baseStart_2141269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141292 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_2141292 : Nat := 118140960795 + 2141292 * 2 ^ 59
def prefixEnd_2141292 : Nat := 4983230072969 + 3 ^ 40 * 2141292 * 2
def baseEnd_2141292 : Nat := 366504005875780472967461

theorem tailTrace_2141292 : CollatzResearch.WordTrace tailWord_2141292 prefixEnd_2141292 366504005875780472967461 := by
  unfold tailWord_2141292
  simp only [CollatzResearch.WordTrace]
  refine ⟨39049667679236131201781065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52066223572314841602374753 39049667679236131201781065)
  ·
    refine ⟨29287250759427098401335799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39049667679236131201781065 29287250759427098401335799)
    ·
      refine ⟨43930876139140647602003699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29287250759427098401335799 43930876139140647602003699)
      ·
        refine ⟨65896314208710971403005549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43930876139140647602003699 65896314208710971403005549)
        ·
          refine ⟨24711117828266614276127081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65896314208710971403005549 24711117828266614276127081)
          ·
            refine ⟨18533338371199960707095311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24711117828266614276127081 18533338371199960707095311)
            ·
              refine ⟨27800007556799941060642967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18533338371199960707095311 27800007556799941060642967)
              ·
                refine ⟨41700011335199911590964451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27800007556799941060642967 41700011335199911590964451)
                ·
                  refine ⟨62550017002799867386446677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41700011335199911590964451 62550017002799867386446677)
                  ·
                    refine ⟨366504005875780472967461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 62550017002799867386446677 366504005875780472967461)
                    ·
                      rfl

theorem cell23_2141292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_2141292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141292 prefixEnd_2141292 := by exact prefixLift 2141292
  have htrace : WordTrace (prefixWord ++ tailWord_2141292) baseStart_2141292 baseEnd_2141292 := by
    simpa [prefixWord, tailWord_2141292, baseEnd_2141292] using wordTrace_append hprefix tailTrace_2141292
  have hstable : (prefixWord ++ tailWord_2141292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141292).length < 2 ^ (prefixWord ++ tailWord_2141292).sum := by decide
  have hdescent : baseEnd_2141292 < baseStart_2141292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141340 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2141340 : Nat := 118140960795 + 2141340 * 2 ^ 59
def prefixEnd_2141340 : Nat := 4983230072969 + 3 ^ 40 * 2141340 * 2
def baseEnd_2141340 : Nat := 1099536664698757231102163

theorem tailTrace_2141340 : CollatzResearch.WordTrace tailWord_2141340 prefixEnd_2141340 1099536664698757231102163 := by
  unfold tailWord_2141340
  simp only [CollatzResearch.WordTrace]
  refine ⟨39050543031149183300654737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52067390708198911067539649 39050543031149183300654737)
  ·
    refine ⟨29287907273361887475491053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39050543031149183300654737 29287907273361887475491053)
    ·
      refine ⟨10982965227510707803309145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29287907273361887475491053 10982965227510707803309145)
      ·
        refine ⟨8237223920633030852481859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10982965227510707803309145 8237223920633030852481859)
        ·
          refine ⟨12355835880949546278722789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8237223920633030852481859 12355835880949546278722789)
          ·
            refine ⟨2316719227678039927260523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12355835880949546278722789 2316719227678039927260523)
            ·
              refine ⟨3475078841517059890890785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316719227678039927260523 3475078841517059890890785)
              ·
                refine ⟨2606309131137794918168089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3475078841517059890890785 2606309131137794918168089)
                ·
                  refine ⟨1954731848353346188626067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2606309131137794918168089 1954731848353346188626067)
                  ·
                    refine ⟨2932097772530019282939101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954731848353346188626067 2932097772530019282939101)
                    ·
                      refine ⟨1099536664698757231102163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932097772530019282939101 1099536664698757231102163)
                      ·
                        rfl

theorem cell23_2141340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2141340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141340 prefixEnd_2141340 := by exact prefixLift 2141340
  have htrace : WordTrace (prefixWord ++ tailWord_2141340) baseStart_2141340 baseEnd_2141340 := by
    simpa [prefixWord, tailWord_2141340, baseEnd_2141340] using wordTrace_append hprefix tailTrace_2141340
  have hstable : (prefixWord ++ tailWord_2141340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141340).length < 2 ^ (prefixWord ++ tailWord_2141340).sum := by decide
  have hdescent : baseEnd_2141340 < baseStart_2141340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141357 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_2141357 : Nat := 118140960795 + 2141357 * 2 ^ 59
def prefixEnd_2141357 : Nat := 4983230072969 + 3 ^ 40 * 2141357 * 2
def baseEnd_2141357 : Nat := 1099545393869883664589585

theorem tailTrace_2141357 : CollatzResearch.WordTrace tailWord_2141357 prefixEnd_2141357 1099545393869883664589585 := by
  unfold tailWord_2141357
  simp only [CollatzResearch.WordTrace]
  refine ⟨78101706103236778504678325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52067804068824519003118883 78101706103236778504678325)
  ·
    refine ⟨7322034947178447984813593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78101706103236778504678325 7322034947178447984813593)
    ·
      refine ⟨5491526210383835988610195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7322034947178447984813593 5491526210383835988610195)
      ·
        refine ⟨8237289315575753982915293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5491526210383835988610195 8237289315575753982915293)
        ·
          refine ⟨3088983493340907743593235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8237289315575753982915293 3088983493340907743593235)
          ·
            refine ⟨4633475240011361615389853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3088983493340907743593235 4633475240011361615389853)
            ·
              refine ⟨1737553215004260605771195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4633475240011361615389853 1737553215004260605771195)
              ·
                refine ⟨2606329822506390908656793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1737553215004260605771195 2606329822506390908656793)
                ·
                  refine ⟨1954747366879793181492595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2606329822506390908656793 1954747366879793181492595)
                  ·
                    refine ⟨2932121050319689772238893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954747366879793181492595 2932121050319689772238893)
                    ·
                      refine ⟨1099545393869883664589585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932121050319689772238893 1099545393869883664589585)
                      ·
                        rfl

theorem cell23_2141357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_2141357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141357 prefixEnd_2141357 := by exact prefixLift 2141357
  have htrace : WordTrace (prefixWord ++ tailWord_2141357) baseStart_2141357 baseEnd_2141357 := by
    simpa [prefixWord, tailWord_2141357, baseEnd_2141357] using wordTrace_append hprefix tailTrace_2141357
  have hstable : (prefixWord ++ tailWord_2141357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141357).length < 2 ^ (prefixWord ++ tailWord_2141357).sum := by decide
  have hdescent : baseEnd_2141357 < baseStart_2141357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141359 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_2141359 : Nat := 118140960795 + 2141359 * 2 ^ 59
def prefixEnd_2141359 : Nat := 4983230072969 + 3 ^ 40 * 2141359 * 2
def baseEnd_2141359 : Nat := 1099546420831192656764575

theorem tailTrace_2141359 : CollatzResearch.WordTrace tailWord_2141359 prefixEnd_2141359 1099546420831192656764575 := by
  unfold tailWord_2141359
  simp only [CollatzResearch.WordTrace]
  refine ⟨78101779049229532846251131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52067852699486355230834087 78101779049229532846251131)
  ·
    refine ⟨117152668573844299269376697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78101779049229532846251131 117152668573844299269376697)
    ·
      refine ⟨87864501430383224452032523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117152668573844299269376697 87864501430383224452032523)
      ·
        refine ⟨131796752145574836678048785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87864501430383224452032523 131796752145574836678048785)
        ·
          refine ⟨98847564109181127508536589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131796752145574836678048785 98847564109181127508536589)
          ·
            refine ⟨37067836540942922815701221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98847564109181127508536589 37067836540942922815701221)
            ·
              refine ⟨6950219351426798027943979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37067836540942922815701221 6950219351426798027943979)
              ·
                refine ⟨10425329027140197041915969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6950219351426798027943979 10425329027140197041915969)
                ·
                  refine ⟨7818996770355147781436977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10425329027140197041915969 7818996770355147781436977)
                  ·
                    refine ⟨5864247577766360836077733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7818996770355147781436977 5864247577766360836077733)
                    ·
                      refine ⟨1099546420831192656764575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5864247577766360836077733 1099546420831192656764575)
                      ·
                        rfl

theorem cell23_2141359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_2141359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141359 prefixEnd_2141359 := by exact prefixLift 2141359
  have htrace : WordTrace (prefixWord ++ tailWord_2141359) baseStart_2141359 baseEnd_2141359 := by
    simpa [prefixWord, tailWord_2141359, baseEnd_2141359] using wordTrace_append hprefix tailTrace_2141359
  have hstable : (prefixWord ++ tailWord_2141359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141359).length < 2 ^ (prefixWord ++ tailWord_2141359).sum := by decide
  have hdescent : baseEnd_2141359 < baseStart_2141359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141363 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 2, 2, 2]
def baseStart_2141363 : Nat := 118140960795 + 2141363 * 2 ^ 59
def prefixEnd_2141363 : Nat := 4983230072969 + 3 ^ 40 * 2141363 * 2
def baseEnd_2141363 : Nat := 1099548474753810641114557

theorem tailTrace_2141363 : CollatzResearch.WordTrace tailWord_2141363 prefixEnd_2141363 1099548474753810641114557 := by
  unfold tailWord_2141363
  simp only [CollatzResearch.WordTrace]
  refine ⟨78101924941215041529396743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52067949960810027686264495 78101924941215041529396743)
  ·
    refine ⟨117152887411822562294095115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78101924941215041529396743 117152887411822562294095115)
    ·
      refine ⟨175729331117733843441142673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117152887411822562294095115 175729331117733843441142673)
      ·
        refine ⟨131796998338300382580857005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175729331117733843441142673 131796998338300382580857005)
        ·
          refine ⟨49423874376862643467821377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131796998338300382580857005 49423874376862643467821377)
          ·
            refine ⟨37067905782646982600866033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49423874376862643467821377 37067905782646982600866033)
            ·
              refine ⟨27800929336985236950649525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37067905782646982600866033 27800929336985236950649525)
              ·
                refine ⟨2606337125342365964123393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27800929336985236950649525 2606337125342365964123393)
                ·
                  refine ⟨1954752844006774473092545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2606337125342365964123393 1954752844006774473092545)
                  ·
                    refine ⟨1466064633005080854819409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1954752844006774473092545 1466064633005080854819409)
                    ·
                      refine ⟨1099548474753810641114557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466064633005080854819409 1099548474753810641114557)
                      ·
                        rfl

theorem cell23_2141363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 2, 2].length) (baseStart_2141363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141363 prefixEnd_2141363 := by exact prefixLift 2141363
  have htrace : WordTrace (prefixWord ++ tailWord_2141363) baseStart_2141363 baseEnd_2141363 := by
    simpa [prefixWord, tailWord_2141363, baseEnd_2141363] using wordTrace_append hprefix tailTrace_2141363
  have hstable : (prefixWord ++ tailWord_2141363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141363).length < 2 ^ (prefixWord ++ tailWord_2141363).sum := by decide
  have hdescent : baseEnd_2141363 < baseStart_2141363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141369 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 7]
def baseStart_2141369 : Nat := 118140960795 + 2141369 * 2 ^ 59
def prefixEnd_2141369 : Nat := 4983230072969 + 3 ^ 40 * 2141369 * 2
def baseEnd_2141369 : Nat := 122172395070859735293281

theorem tailTrace_2141369 : CollatzResearch.WordTrace tailWord_2141369 prefixEnd_2141369 122172395070859735293281 := by
  unfold tailWord_2141369
  simp only [CollatzResearch.WordTrace]
  refine ⟨78102143779193304554115161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52068095852795536369410107 78102143779193304554115161)
  ·
    refine ⟨58576607834394978415586371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78102143779193304554115161 58576607834394978415586371)
    ·
      refine ⟨87864911751592467623379557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58576607834394978415586371 87864911751592467623379557)
      ·
        refine ⟨16474670953423587679383667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87864911751592467623379557 16474670953423587679383667)
        ·
          refine ⟨24712006430135381519075501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16474670953423587679383667 24712006430135381519075501)
          ·
            refine ⟨9267002411300768069653313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24712006430135381519075501 9267002411300768069653313)
            ·
              refine ⟨6950251808475576052239985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9267002411300768069653313 6950251808475576052239985)
              ·
                refine ⟨5212688856356682039179989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6950251808475576052239985 5212688856356682039179989)
                ·
                  refine ⟨122172395070859735293281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5212688856356682039179989 122172395070859735293281)
                  ·
                    rfl

theorem cell23_2141369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_2141369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141369 prefixEnd_2141369 := by exact prefixLift 2141369
  have htrace : WordTrace (prefixWord ++ tailWord_2141369) baseStart_2141369 baseEnd_2141369 := by
    simpa [prefixWord, tailWord_2141369, baseEnd_2141369] using wordTrace_append hprefix tailTrace_2141369
  have hstable : (prefixWord ++ tailWord_2141369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141369).length < 2 ^ (prefixWord ++ tailWord_2141369).sum := by decide
  have hdescent : baseEnd_2141369 < baseStart_2141369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141379 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 3]
def baseStart_2141379 : Nat := 118140960795 + 2141379 * 2 ^ 59
def prefixEnd_2141379 : Nat := 4983230072969 + 3 ^ 40 * 2141379 * 2
def baseEnd_2141379 : Nat := 1099556690444282578514483

theorem tailTrace_2141379 : CollatzResearch.WordTrace tailWord_2141379 prefixEnd_2141379 1099556690444282578514483 := by
  unfold tailWord_2141379
  simp only [CollatzResearch.WordTrace]
  refine ⟨78102508509157076261979191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52068339006104717507986127 78102508509157076261979191)
  ·
    refine ⟨117153762763735614392968787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78102508509157076261979191 117153762763735614392968787)
    ·
      refine ⟨175730644145603421589453181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117153762763735614392968787 175730644145603421589453181)
      ·
        refine ⟨65898991554601283096044943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175730644145603421589453181 65898991554601283096044943)
        ·
          refine ⟨98848487331901924644067415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65898991554601283096044943 98848487331901924644067415)
          ·
            refine ⟨148272730997852886966101123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98848487331901924644067415 148272730997852886966101123)
            ·
              refine ⟨222409096496779330449151685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148272730997852886966101123 222409096496779330449151685)
              ·
                refine ⟨41701705593146124459215941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222409096496779330449151685 41701705593146124459215941)
                ·
                  refine ⟨7819069798714898336102989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41701705593146124459215941 7819069798714898336102989)
                  ·
                    refine ⟨2932151174518086876038621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7819069798714898336102989 2932151174518086876038621)
                    ·
                      refine ⟨1099556690444282578514483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932151174518086876038621 1099556690444282578514483)
                      ·
                        rfl

theorem cell23_2141379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_2141379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141379 prefixEnd_2141379 := by exact prefixLift 2141379
  have htrace : WordTrace (prefixWord ++ tailWord_2141379) baseStart_2141379 baseEnd_2141379 := by
    simpa [prefixWord, tailWord_2141379, baseEnd_2141379] using wordTrace_append hprefix tailTrace_2141379
  have hstable : (prefixWord ++ tailWord_2141379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141379).length < 2 ^ (prefixWord ++ tailWord_2141379).sum := by decide
  have hdescent : baseEnd_2141379 < baseStart_2141379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141399 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 4, 5]
def baseStart_2141399 : Nat := 118140960795 + 2141399 * 2 ^ 59
def prefixEnd_2141399 : Nat := 4983230072969 + 3 ^ 40 * 2141399 * 2
def baseEnd_2141399 : Nat := 366522320019124166754797

theorem tailTrace_2141399 : CollatzResearch.WordTrace tailWord_2141399 prefixEnd_2141399 366522320019124166754797 := by
  unfold tailWord_2141399
  simp only [CollatzResearch.WordTrace]
  refine ⟨78103237969084619677707251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52068825312723079785138167 78103237969084619677707251)
  ·
    refine ⟨117154856953626929516560877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78103237969084619677707251 117154856953626929516560877)
    ·
      refine ⟨43933071357610098568710329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117154856953626929516560877 43933071357610098568710329)
      ·
        refine ⟨32949803518207573926532747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43933071357610098568710329 32949803518207573926532747)
        ·
          refine ⟨49424705277311360889799121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32949803518207573926532747 49424705277311360889799121)
          ·
            refine ⟨37068528957983520667349341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49424705277311360889799121 37068528957983520667349341)
            ·
              refine ⟨13900698359243820250256003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37068528957983520667349341 13900698359243820250256003)
              ·
                refine ⟨20851047538865730375384005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13900698359243820250256003 20851047538865730375384005)
                ·
                  refine ⟨3909571413537324445384501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20851047538865730375384005 3909571413537324445384501)
                  ·
                    refine ⟨366522320019124166754797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3909571413537324445384501 366522320019124166754797)
                    ·
                      rfl

theorem cell23_2141399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_2141399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141399 prefixEnd_2141399 := by exact prefixLift 2141399
  have htrace : WordTrace (prefixWord ++ tailWord_2141399) baseStart_2141399 baseEnd_2141399 := by
    simpa [prefixWord, tailWord_2141399, baseEnd_2141399] using wordTrace_append hprefix tailTrace_2141399
  have hstable : (prefixWord ++ tailWord_2141399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141399).length < 2 ^ (prefixWord ++ tailWord_2141399).sum := by decide
  have hdescent : baseEnd_2141399 < baseStart_2141399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141409 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_2141409 : Nat := 118140960795 + 2141409 * 2 ^ 59
def prefixEnd_2141409 : Nat := 4983230072969 + 3 ^ 40 * 2141409 * 2
def baseEnd_2141409 : Nat := 1099572094863917461139345

theorem tailTrace_2141409 : CollatzResearch.WordTrace tailWord_2141409 prefixEnd_2141409 1099572094863917461139345 := by
  unfold tailWord_2141409
  simp only [CollatzResearch.WordTrace]
  refine ⟨78103602699048391385571281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52069068466032260923714187 78103602699048391385571281)
  ·
    refine ⟨58577702024286293539178461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78103602699048391385571281 58577702024286293539178461)
    ·
      refine ⟨21966638259107360077191923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58577702024286293539178461 21966638259107360077191923)
      ·
        refine ⟨32949957388661040115787885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21966638259107360077191923 32949957388661040115787885)
        ·
          refine ⟨12356234020747890043420457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32949957388661040115787885 12356234020747890043420457)
          ·
            refine ⟨9267175515560917532565343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12356234020747890043420457 9267175515560917532565343)
            ·
              refine ⟨13900763273341376298848015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9267175515560917532565343 13900763273341376298848015)
              ·
                refine ⟨20851144910012064448272023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13900763273341376298848015 20851144910012064448272023)
                ·
                  refine ⟨31276717365018096672408035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20851144910012064448272023 31276717365018096672408035)
                  ·
                    refine ⟨46915076047527145008612053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31276717365018096672408035 46915076047527145008612053)
                    ·
                      refine ⟨1099572094863917461139345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46915076047527145008612053 1099572094863917461139345)
                      ·
                        rfl

theorem cell23_2141409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_2141409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141409 prefixEnd_2141409 := by exact prefixLift 2141409
  have htrace : WordTrace (prefixWord ++ tailWord_2141409) baseStart_2141409 baseEnd_2141409 := by
    simpa [prefixWord, tailWord_2141409, baseEnd_2141409] using wordTrace_append hprefix tailTrace_2141409
  have hstable : (prefixWord ++ tailWord_2141409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141409).length < 2 ^ (prefixWord ++ tailWord_2141409).sum := by decide
  have hdescent : baseEnd_2141409 < baseStart_2141409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141449 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_2141449 : Nat := 118140960795 + 2141449 * 2 ^ 59
def prefixEnd_2141449 : Nat := 4983230072969 + 3 ^ 40 * 2141449 * 2
def baseEnd_2141449 : Nat := 1099592634090097304639161

theorem tailTrace_2141449 : CollatzResearch.WordTrace tailWord_2141449 prefixEnd_2141449 1099592634090097304639161 := by
  unfold tailWord_2141449
  simp only [CollatzResearch.WordTrace]
  refine ⟨78105061618903478217027401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52070041079268985478018267 78105061618903478217027401)
  ·
    refine ⟨58578796214177608662770551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78105061618903478217027401 58578796214177608662770551)
    ·
      refine ⟨87868194321266412994155827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58578796214177608662770551 87868194321266412994155827)
      ·
        refine ⟨131802291481899619491233741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87868194321266412994155827 131802291481899619491233741)
        ·
          refine ⟨49425859305712357309212653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131802291481899619491233741 49425859305712357309212653)
          ·
            refine ⟨18534697239642133990954745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49425859305712357309212653 18534697239642133990954745)
            ·
              refine ⟨13901022929731600493216059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18534697239642133990954745 13901022929731600493216059)
              ·
                refine ⟨20851534394597400739824089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13901022929731600493216059 20851534394597400739824089)
                ·
                  refine ⟨15638650795948050554868067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20851534394597400739824089 15638650795948050554868067)
                  ·
                    refine ⟨23457976193922075832302101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15638650795948050554868067 23457976193922075832302101)
                    ·
                      refine ⟨1099592634090097304639161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23457976193922075832302101 1099592634090097304639161)
                      ·
                        rfl

theorem cell23_2141449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_2141449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141449 prefixEnd_2141449 := by exact prefixLift 2141449
  have htrace : WordTrace (prefixWord ++ tailWord_2141449) baseStart_2141449 baseEnd_2141449 := by
    simpa [prefixWord, tailWord_2141449, baseEnd_2141449] using wordTrace_append hprefix tailTrace_2141449
  have hstable : (prefixWord ++ tailWord_2141449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141449).length < 2 ^ (prefixWord ++ tailWord_2141449).sum := by decide
  have hdescent : baseEnd_2141449 < baseStart_2141449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141476 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 6]
def baseStart_2141476 : Nat := 118140960795 + 2141476 * 2 ^ 59
def prefixEnd_2141476 : Nat := 4983230072969 + 3 ^ 40 * 2141476 * 2
def baseEnd_2141476 : Nat := 122178499785307633222393

theorem tailTrace_2141476 : CollatzResearch.WordTrace tailWord_2141476 prefixEnd_2141476 122178499785307633222393 := by
  unfold tailWord_2141476
  simp only [CollatzResearch.WordTrace]
  refine ⟨39053023194902830914130141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52070697593203774552173521 39053023194902830914130141)
  ·
    refine ⟨14644883698088561592798803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39053023194902830914130141 14644883698088561592798803)
    ·
      refine ⟨21967325547132842389198205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14644883698088561592798803 21967325547132842389198205)
      ·
        refine ⟨8237747080174815895949327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21967325547132842389198205 8237747080174815895949327)
        ·
          refine ⟨12356620620262223843923991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8237747080174815895949327 12356620620262223843923991)
          ·
            refine ⟨18534930930393335765885987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12356620620262223843923991 18534930930393335765885987)
            ·
              refine ⟨27802396395590003648828981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18534930930393335765885987 27802396395590003648828981)
              ·
                refine ⟨2606474662086562842077717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27802396395590003648828981 2606474662086562842077717)
                ·
                  refine ⟨122178499785307633222393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2606474662086562842077717 122178499785307633222393)
                  ·
                    rfl

theorem cell23_2141476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_2141476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141476 prefixEnd_2141476 := by exact prefixLift 2141476
  have htrace : WordTrace (prefixWord ++ tailWord_2141476) baseStart_2141476 baseEnd_2141476 := by
    simpa [prefixWord, tailWord_2141476, baseEnd_2141476] using wordTrace_append hprefix tailTrace_2141476
  have hstable : (prefixWord ++ tailWord_2141476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141476).length < 2 ^ (prefixWord ++ tailWord_2141476).sum := by decide
  have hdescent : baseEnd_2141476 < baseStart_2141476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141490 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2141490 : Nat := 118140960795 + 2141490 * 2 ^ 59
def prefixEnd_2141490 : Nat := 4983230072969 + 3 ^ 40 * 2141490 * 2
def baseEnd_2141490 : Nat := 1099613686796931644226473

theorem tailTrace_2141490 : CollatzResearch.WordTrace tailWord_2141490 prefixEnd_2141490 1099613686796931644226473 := by
  unfold tailWord_2141490
  simp only [CollatzResearch.WordTrace]
  refine ⟨19526639252938735554817481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52071038007836628146179949 19526639252938735554817481)
  ·
    refine ⟨14644979439704051666113111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19526639252938735554817481 14644979439704051666113111)
    ·
      refine ⟨21967469159556077499169667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14644979439704051666113111 21967469159556077499169667)
      ·
        refine ⟨32951203739334116248754501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21967469159556077499169667 32951203739334116248754501)
        ·
          refine ⟨6178350701125146796641469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32951203739334116248754501 6178350701125146796641469)
          ·
            refine ⟨2316881512921930048740551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6178350701125146796641469 2316881512921930048740551)
            ·
              refine ⟨3475322269382895073110827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316881512921930048740551 3475322269382895073110827)
              ·
                refine ⟨5212983404074342609666241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475322269382895073110827 5212983404074342609666241)
                ·
                  refine ⟨3909737553055756957249681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5212983404074342609666241 3909737553055756957249681)
                  ·
                    refine ⟨2932303164791817717937261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909737553055756957249681 2932303164791817717937261)
                    ·
                      refine ⟨1099613686796931644226473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932303164791817717937261 1099613686796931644226473)
                      ·
                        rfl

theorem cell23_2141490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2141490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141490 prefixEnd_2141490 := by exact prefixLift 2141490
  have htrace : WordTrace (prefixWord ++ tailWord_2141490) baseStart_2141490 baseEnd_2141490 := by
    simpa [prefixWord, tailWord_2141490, baseEnd_2141490] using wordTrace_append hprefix tailTrace_2141490
  have hstable : (prefixWord ++ tailWord_2141490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141490).length < 2 ^ (prefixWord ++ tailWord_2141490).sum := by decide
  have hdescent : baseEnd_2141490 < baseStart_2141490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141497 : List Nat := [1, 2, 1, 6, 2, 1, 2, 3, 1, 4]
def baseStart_2141497 : Nat := 118140960795 + 2141497 * 2 ^ 59
def prefixEnd_2141497 : Nat := 4983230072969 + 3 ^ 40 * 2141497 * 2
def baseEnd_2141497 : Nat := 366539093720504372279647

theorem tailTrace_2141497 : CollatzResearch.WordTrace tailWord_2141497 prefixEnd_2141497 366539093720504372279647 := by
  unfold tailWord_2141497
  simp only [CollatzResearch.WordTrace]
  refine ⟨78106812322729582414774745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52071208215153054943183163 78106812322729582414774745)
  ·
    refine ⟨58580109242047186811081059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78106812322729582414774745 58580109242047186811081059)
    ·
      refine ⟨87870163863070780216621589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58580109242047186811081059 87870163863070780216621589)
      ·
        refine ⟨4118913931081442822654137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87870163863070780216621589 4118913931081442822654137)
        ·
          refine ⟨3089185448311082116990603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118913931081442822654137 3089185448311082116990603)
          ·
            refine ⟨4633778172466623175485905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089185448311082116990603 4633778172466623175485905)
            ·
              refine ⟨3475333629349967381614429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4633778172466623175485905 3475333629349967381614429)
              ·
                refine ⟨1303250111006237768105411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3475333629349967381614429 1303250111006237768105411)
                ·
                  refine ⟨1954875166509356652158117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303250111006237768105411 1954875166509356652158117)
                  ·
                    refine ⟨366539093720504372279647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954875166509356652158117 366539093720504372279647)
                    ·
                      rfl

theorem cell23_2141497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 4].length) (baseStart_2141497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141497 prefixEnd_2141497 := by exact prefixLift 2141497
  have htrace : WordTrace (prefixWord ++ tailWord_2141497) baseStart_2141497 baseEnd_2141497 := by
    simpa [prefixWord, tailWord_2141497, baseEnd_2141497] using wordTrace_append hprefix tailTrace_2141497
  have hstable : (prefixWord ++ tailWord_2141497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141497).length < 2 ^ (prefixWord ++ tailWord_2141497).sum := by decide
  have hdescent : baseEnd_2141497 < baseStart_2141497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141513 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 2, 3, 2]
def baseStart_2141513 : Nat := 118140960795 + 2141513 * 2 ^ 59
def prefixEnd_2141513 : Nat := 4983230072969 + 3 ^ 40 * 2141513 * 2
def baseEnd_2141513 : Nat := 1099625496851985054238867

theorem tailTrace_2141513 : CollatzResearch.WordTrace tailWord_2141513 prefixEnd_2141513 1099625496851985054238867 := by
  unfold tailWord_2141513
  simp only [CollatzResearch.WordTrace]
  refine ⟨78107395890671617147357193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52071597260447744764904795 78107395890671617147357193)
  ·
    refine ⟨58580546918003712860517895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78107395890671617147357193 58580546918003712860517895)
    ·
      refine ⟨87870820377005569290776843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58580546918003712860517895 87870820377005569290776843)
      ·
        refine ⟨131806230565508353936165265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87870820377005569290776843 131806230565508353936165265)
        ·
          refine ⟨98854672924131265452123949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131806230565508353936165265 98854672924131265452123949)
          ·
            refine ⟨37070502346549224544546481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98854672924131265452123949 37070502346549224544546481)
            ·
              refine ⟨27802876759911918408409861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37070502346549224544546481 27802876759911918408409861)
              ·
                refine ⟨5213039392483484701576849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27802876759911918408409861 5213039392483484701576849)
                ·
                  refine ⟨3909779544362613526182637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213039392483484701576849 3909779544362613526182637)
                  ·
                    refine ⟨1466167329135980072318489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3909779544362613526182637 1466167329135980072318489)
                    ·
                      refine ⟨1099625496851985054238867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466167329135980072318489 1099625496851985054238867)
                      ·
                        rfl

theorem cell23_2141513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 3, 2].length) (baseStart_2141513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141513 prefixEnd_2141513 := by exact prefixLift 2141513
  have htrace : WordTrace (prefixWord ++ tailWord_2141513) baseStart_2141513 baseEnd_2141513 := by
    simpa [prefixWord, tailWord_2141513, baseEnd_2141513] using wordTrace_append hprefix tailTrace_2141513
  have hstable : (prefixWord ++ tailWord_2141513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141513).length < 2 ^ (prefixWord ++ tailWord_2141513).sum := by decide
  have hdescent : baseEnd_2141513 < baseStart_2141513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141520 : List Nat := [2, 1, 1, 1, 1, 5, 1, 6, 1, 1, 3]
def baseStart_2141520 : Nat := 118140960795 + 2141520 * 2 ^ 59
def prefixEnd_2141520 : Nat := 4983230072969 + 3 ^ 40 * 2141520 * 2
def baseEnd_2141520 : Nat := 1099629091216566526851335

theorem tailTrace_2141520 : CollatzResearch.WordTrace tailWord_2141520 prefixEnd_2141520 1099629091216566526851335 := by
  unfold tailWord_2141520
  simp only [CollatzResearch.WordTrace]
  refine ⟨39053825600823128671431007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52071767467764171561908009 39053825600823128671431007)
  ·
    refine ⟨58580738401234693007146511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39053825600823128671431007 58580738401234693007146511)
    ·
      refine ⟨87871107601852039510719767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58580738401234693007146511 87871107601852039510719767)
      ·
        refine ⟨131806661402778059266079651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87871107601852039510719767 131806661402778059266079651)
        ·
          refine ⟨197709992104167088899119477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131806661402778059266079651 197709992104167088899119477)
          ·
            refine ⟨18535311759765664584292451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 197709992104167088899119477 18535311759765664584292451)
            ·
              refine ⟨27802967639648496876438677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18535311759765664584292451 27802967639648496876438677)
              ·
                refine ⟨1303264108108523291083063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27802967639648496876438677 1303264108108523291083063)
                ·
                  refine ⟨1954896162162784936624595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303264108108523291083063 1954896162162784936624595)
                  ·
                    refine ⟨2932344243244177404936893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1954896162162784936624595 2932344243244177404936893)
                    ·
                      refine ⟨1099629091216566526851335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932344243244177404936893 1099629091216566526851335)
                      ·
                        rfl

theorem cell23_2141520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 1, 3].length) (baseStart_2141520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141520 prefixEnd_2141520 := by exact prefixLift 2141520
  have htrace : WordTrace (prefixWord ++ tailWord_2141520) baseStart_2141520 baseEnd_2141520 := by
    simpa [prefixWord, tailWord_2141520, baseEnd_2141520] using wordTrace_append hprefix tailTrace_2141520
  have hstable : (prefixWord ++ tailWord_2141520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141520).length < 2 ^ (prefixWord ++ tailWord_2141520).sum := by decide
  have hdescent : baseEnd_2141520 < baseStart_2141520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141563 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 3]
def baseStart_2141563 : Nat := 118140960795 + 2141563 * 2 ^ 59
def prefixEnd_2141563 : Nat := 4983230072969 + 3 ^ 40 * 2141563 * 2
def baseEnd_2141563 : Nat := 1099651170884709858613637

theorem tailTrace_2141563 : CollatzResearch.WordTrace tailWord_2141563 prefixEnd_2141563 1099651170884709858613637 := by
  unfold tailWord_2141563
  simp only [CollatzResearch.WordTrace]
  refine ⟨78109219540490475686677343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52072813026993650457784895 78109219540490475686677343)
  ·
    refine ⟨117163829310735713530016015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78109219540490475686677343 117163829310735713530016015)
    ·
      refine ⟨175745743966103570295024023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117163829310735713530016015 175745743966103570295024023)
      ·
        refine ⟨263618615949155355442536035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175745743966103570295024023 263618615949155355442536035)
        ·
          refine ⟨395427923923733033163804053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263618615949155355442536035 395427923923733033163804053)
          ·
            refine ⟨18535683933924985929553315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 395427923923733033163804053 18535683933924985929553315)
            ·
              refine ⟨27803525900887478894329973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18535683933924985929553315 27803525900887478894329973)
              ·
                refine ⟨2606580553208201146343435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27803525900887478894329973 2606580553208201146343435)
                ·
                  refine ⟨3909870829812301719515153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606580553208201146343435 3909870829812301719515153)
                  ·
                    refine ⟨2932403122359226289636365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909870829812301719515153 2932403122359226289636365)
                    ·
                      refine ⟨1099651170884709858613637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932403122359226289636365 1099651170884709858613637)
                      ·
                        rfl

theorem cell23_2141563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 3].length) (baseStart_2141563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141563 prefixEnd_2141563 := by exact prefixLift 2141563
  have htrace : WordTrace (prefixWord ++ tailWord_2141563) baseStart_2141563 baseEnd_2141563 := by
    simpa [prefixWord, tailWord_2141563, baseEnd_2141563] using wordTrace_append hprefix tailTrace_2141563
  have hstable : (prefixWord ++ tailWord_2141563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141563).length < 2 ^ (prefixWord ++ tailWord_2141563).sum := by decide
  have hdescent : baseEnd_2141563 < baseStart_2141563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141597 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_2141597 : Nat := 118140960795 + 2141597 * 2 ^ 59
def prefixEnd_2141597 : Nat := 4983230072969 + 3 ^ 40 * 2141597 * 2
def baseEnd_2141597 : Nat := 1099668629226962725588481

theorem tailTrace_2141597 : CollatzResearch.WordTrace tailWord_2141597 prefixEnd_2141597 1099668629226962725588481 := by
  unfold tailWord_2141597
  simp only [CollatzResearch.WordTrace]
  refine ⟨78110459622367299493415045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52073639748244866328943363 78110459622367299493415045)
  ·
    refine ⟨14645711179193868655015321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78110459622367299493415045 14645711179193868655015321)
    ·
      refine ⟨10984283384395401491261491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14645711179193868655015321 10984283384395401491261491)
      ·
        refine ⟨16476425076593102236892237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10984283384395401491261491 16476425076593102236892237)
        ·
          refine ⟨6178659403722413338834589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16476425076593102236892237 6178659403722413338834589)
          ·
            refine ⟨2316997276395905002062971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6178659403722413338834589 2316997276395905002062971)
            ·
              refine ⟨3475495914593857503094457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2316997276395905002062971 3475495914593857503094457)
              ·
                refine ⟨2606621935945393127320843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3475495914593857503094457 2606621935945393127320843)
                ·
                  refine ⟨3909932903918089690981265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606621935945393127320843 3909932903918089690981265)
                  ·
                    refine ⟨2932449677938567268235949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909932903918089690981265 2932449677938567268235949)
                    ·
                      refine ⟨1099668629226962725588481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932449677938567268235949 1099668629226962725588481)
                      ·
                        rfl

theorem cell23_2141597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_2141597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141597 prefixEnd_2141597 := by exact prefixLift 2141597
  have htrace : WordTrace (prefixWord ++ tailWord_2141597) baseStart_2141597 baseEnd_2141597 := by
    simpa [prefixWord, tailWord_2141597, baseEnd_2141597] using wordTrace_append hprefix tailTrace_2141597
  have hstable : (prefixWord ++ tailWord_2141597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141597).length < 2 ^ (prefixWord ++ tailWord_2141597).sum := by decide
  have hdescent : baseEnd_2141597 < baseStart_2141597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141628 : List Nat := [2, 2, 2, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_2141628 : Nat := 118140960795 + 2141628 * 2 ^ 59
def prefixEnd_2141628 : Nat := 4983230072969 + 3 ^ 40 * 2141628 * 2
def baseEnd_2141628 : Nat := 1099684547127252104300839

theorem tailTrace_2141628 : CollatzResearch.WordTrace tailWord_2141628 prefixEnd_2141628 1099684547127252104300839 := by
  unfold tailWord_2141628
  simp only [CollatzResearch.WordTrace]
  refine ⟨39055795142627495893896769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52074393523503327858529025 39055795142627495893896769)
  ·
    refine ⟨29291846356970621920422577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39055795142627495893896769 29291846356970621920422577)
    ·
      refine ⟨21968884767727966440316933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29291846356970621920422577 21968884767727966440316933)
      ·
        refine ⟨4119165893948993707559425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21968884767727966440316933 4119165893948993707559425)
        ·
          refine ⟨3089374420461745280669569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4119165893948993707559425 3089374420461745280669569)
          ·
            refine ⟨2317030815346308960502177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3089374420461745280669569 2317030815346308960502177)
            ·
              refine ⟨1737773111509731720376633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317030815346308960502177 1737773111509731720376633)
              ·
                refine ⟨1303329833632298790282475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1737773111509731720376633 1303329833632298790282475)
                ·
                  refine ⟨1954994750448448185423713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303329833632298790282475 1954994750448448185423713)
                  ·
                    refine ⟨1466246062836336139067785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1954994750448448185423713 1466246062836336139067785)
                    ·
                      refine ⟨1099684547127252104300839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466246062836336139067785 1099684547127252104300839)
                      ·
                        rfl

theorem cell23_2141628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_2141628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141628 prefixEnd_2141628 := by exact prefixLift 2141628
  have htrace : WordTrace (prefixWord ++ tailWord_2141628) baseStart_2141628 baseEnd_2141628 := by
    simpa [prefixWord, tailWord_2141628, baseEnd_2141628] using wordTrace_append hprefix tailTrace_2141628
  have hstable : (prefixWord ++ tailWord_2141628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141628).length < 2 ^ (prefixWord ++ tailWord_2141628).sum := by decide
  have hdescent : baseEnd_2141628 < baseStart_2141628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141653 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2141653 : Nat := 118140960795 + 2141653 * 2 ^ 59
def prefixEnd_2141653 : Nat := 4983230072969 + 3 ^ 40 * 2141653 * 2
def baseEnd_2141653 : Nat := 1099697384143614506488223

theorem tailTrace_2141653 : CollatzResearch.WordTrace tailWord_2141653 prefixEnd_2141653 1099697384143614506488223 := by
  unfold tailWord_2141653
  simp only [CollatzResearch.WordTrace]
  refine ⟨78112502110164421057453613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52075001406776280704969075 78112502110164421057453613)
  ·
    refine ⟨29292188291311657896545105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78112502110164421057453613 29292188291311657896545105)
    ·
      refine ⟨21969141218483743422408829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29292188291311657896545105 21969141218483743422408829)
      ·
        refine ⟨8238427956931403783403311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21969141218483743422408829 8238427956931403783403311)
        ·
          refine ⟨12357641935397105675104967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8238427956931403783403311 12357641935397105675104967)
          ·
            refine ⟨18536462903095658512657451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12357641935397105675104967 18536462903095658512657451)
            ·
              refine ⟨27804694354643487768986177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18536462903095658512657451 27804694354643487768986177)
              ·
                refine ⟨20853520765982615826739633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27804694354643487768986177 20853520765982615826739633)
                ·
                  refine ⟨15640140574486961870054725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20853520765982615826739633 15640140574486961870054725)
                  ·
                    refine ⟨2932526357716305350635261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15640140574486961870054725 2932526357716305350635261)
                    ·
                      refine ⟨1099697384143614506488223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932526357716305350635261 1099697384143614506488223)
                      ·
                        rfl

theorem cell23_2141653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2141653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141653 prefixEnd_2141653 := by exact prefixLift 2141653
  have htrace : WordTrace (prefixWord ++ tailWord_2141653) baseStart_2141653 baseEnd_2141653 := by
    simpa [prefixWord, tailWord_2141653, baseEnd_2141653] using wordTrace_append hprefix tailTrace_2141653
  have hstable : (prefixWord ++ tailWord_2141653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141653).length < 2 ^ (prefixWord ++ tailWord_2141653).sum := by decide
  have hdescent : baseEnd_2141653 < baseStart_2141653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141656 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 9]
def baseStart_2141656 : Nat := 118140960795 + 2141656 * 2 ^ 59
def prefixEnd_2141656 : Nat := 4983230072969 + 3 ^ 40 * 2141656 * 2
def baseEnd_2141656 : Nat := 122188769398397554972301

theorem tailTrace_2141656 : CollatzResearch.WordTrace tailWord_2141656 prefixEnd_2141656 122188769398397554972301 := by
  unfold tailWord_2141656
  simp only [CollatzResearch.WordTrace]
  refine ⟨39056305764576776284906411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52075074352769035046541881 39056305764576776284906411)
  ·
    refine ⟨58584458646865164427359617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39056305764576776284906411 58584458646865164427359617)
    ·
      refine ⟨43938343985148873320519713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58584458646865164427359617 43938343985148873320519713)
      ·
        refine ⟨32953757988861654990389785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43938343985148873320519713 32953757988861654990389785)
        ·
          refine ⟨24715318491646241242792339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32953757988861654990389785 24715318491646241242792339)
          ·
            refine ⟨37072977737469361864188509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24715318491646241242792339 37072977737469361864188509)
            ·
              refine ⟨13902366651551010699070691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37072977737469361864188509 13902366651551010699070691)
              ·
                refine ⟨20853549977326516048606037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13902366651551010699070691 20853549977326516048606037)
                ·
                  refine ⟨122188769398397554972301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20853549977326516048606037 122188769398397554972301)
                  ·
                    rfl

theorem cell23_2141656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 9].length) (baseStart_2141656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141656 prefixEnd_2141656 := by exact prefixLift 2141656
  have htrace : WordTrace (prefixWord ++ tailWord_2141656) baseStart_2141656 baseEnd_2141656 := by
    simpa [prefixWord, tailWord_2141656, baseEnd_2141656] using wordTrace_append hprefix tailTrace_2141656
  have hstable : (prefixWord ++ tailWord_2141656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141656).length < 2 ^ (prefixWord ++ tailWord_2141656).sum := by decide
  have hdescent : baseEnd_2141656 < baseStart_2141656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141703 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 1, 7]
def baseStart_2141703 : Nat := 118140960795 + 2141703 * 2 ^ 59
def prefixEnd_2141703 : Nat := 4983230072969 + 3 ^ 40 * 2141703 * 2
def baseEnd_2141703 : Nat := 366574352725446436954331

theorem tailTrace_2141703 : CollatzResearch.WordTrace tailWord_2141703 prefixEnd_2141703 366574352725446436954331 := by
  unfold tailWord_2141703
  simp only [CollatzResearch.WordTrace]
  refine ⟨78114325759983279596773763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52076217173322186397849175 78114325759983279596773763)
  ·
    refine ⟨117171488639974919395160645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78114325759983279596773763 117171488639974919395160645)
    ·
      refine ⟨21969654119995297386592621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117171488639974919395160645 21969654119995297386592621)
      ·
        refine ⟨8238620294998236519972233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21969654119995297386592621 8238620294998236519972233)
        ·
          refine ⟨6178965221248677389979175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8238620294998236519972233 6178965221248677389979175)
          ·
            refine ⟨9268447831873016084968763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178965221248677389979175 9268447831873016084968763)
            ·
              refine ⟨13902671747809524127453145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9268447831873016084968763 13902671747809524127453145)
              ·
                refine ⟨10427003810857143095589859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13902671747809524127453145 10427003810857143095589859)
                ·
                  refine ⟨15640505716285714643384789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10427003810857143095589859 15640505716285714643384789)
                  ·
                    refine ⟨366574352725446436954331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15640505716285714643384789 366574352725446436954331)
                    ·
                      rfl

theorem cell23_2141703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_2141703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141703 prefixEnd_2141703 := by exact prefixLift 2141703
  have htrace : WordTrace (prefixWord ++ tailWord_2141703) baseStart_2141703 baseEnd_2141703 := by
    simpa [prefixWord, tailWord_2141703, baseEnd_2141703] using wordTrace_append hprefix tailTrace_2141703
  have hstable : (prefixWord ++ tailWord_2141703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141703).length < 2 ^ (prefixWord ++ tailWord_2141703).sum := by decide
  have hdescent : baseEnd_2141703 < baseStart_2141703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141810 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_2141810 : Nat := 118140960795 + 2141810 * 2 ^ 59
def prefixEnd_2141810 : Nat := 4983230072969 + 3 ^ 40 * 2141810 * 2
def baseEnd_2141810 : Nat := 366592666868790130741667

theorem tailTrace_2141810 : CollatzResearch.WordTrace tailWord_2141810 prefixEnd_2141810 366592666868790130741667 := by
  unfold tailWord_2141810
  simp only [CollatzResearch.WordTrace]
  refine ⟨19529557092648909217729721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52078818913730424580612589 19529557092648909217729721)
  ·
    refine ⟨14647167819486681913297291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19529557092648909217729721 14647167819486681913297291)
    ·
      refine ⟨21970751729230022869945937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14647167819486681913297291 21970751729230022869945937)
      ·
        refine ⟨16478063796922517152459453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21970751729230022869945937 16478063796922517152459453)
        ·
          refine ⟨6179273923845943932172295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16478063796922517152459453 6179273923845943932172295)
          ·
            refine ⟨9268910885768915898258443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179273923845943932172295 9268910885768915898258443)
            ·
              refine ⟨13903366328653373847387665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9268910885768915898258443 13903366328653373847387665)
              ·
                refine ⟨10427524746490030385540749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13903366328653373847387665 10427524746490030385540749)
                ·
                  refine ⟨3910321779933761394577781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10427524746490030385540749 3910321779933761394577781)
                  ·
                    refine ⟨366592666868790130741667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3910321779933761394577781 366592666868790130741667)
                    ·
                      rfl

theorem cell23_2141810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_2141810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141810 prefixEnd_2141810 := by exact prefixLift 2141810
  have htrace : WordTrace (prefixWord ++ tailWord_2141810) baseStart_2141810 baseEnd_2141810 := by
    simpa [prefixWord, tailWord_2141810, baseEnd_2141810] using wordTrace_append hprefix tailTrace_2141810
  have hstable : (prefixWord ++ tailWord_2141810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141810).length < 2 ^ (prefixWord ++ tailWord_2141810).sum := by decide
  have hdescent : baseEnd_2141810 < baseStart_2141810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141834 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_2141834 : Nat := 118140960795 + 2141834 * 2 ^ 59
def prefixEnd_2141834 : Nat := 4983230072969 + 3 ^ 40 * 2141834 * 2
def baseEnd_2141834 : Nat := 1099790324142078298324891

theorem tailTrace_2141834 : CollatzResearch.WordTrace tailWord_2141834 prefixEnd_2141834 1099790324142078298324891 := by
  unfold tailWord_2141834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19529775930627172242448139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52079402481672459313195037 19529775930627172242448139)
  ·
    refine ⟨29294663895940758363672209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19529775930627172242448139 29294663895940758363672209)
    ·
      refine ⟨21970997921955568772754157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29294663895940758363672209 21970997921955568772754157)
      ·
        refine ⟨8239124220733338289782809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21970997921955568772754157 8239124220733338289782809)
        ·
          refine ⟨6179343165550003717337107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8239124220733338289782809 6179343165550003717337107)
          ·
            refine ⟨9269014748325005576005661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179343165550003717337107 9269014748325005576005661)
            ·
              refine ⟨3475880530621877091002123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9269014748325005576005661 3475880530621877091002123)
              ·
                refine ⟨5213820795932815636503185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3475880530621877091002123 5213820795932815636503185)
                ·
                  refine ⟨3910365596949611727377389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213820795932815636503185 3910365596949611727377389)
                  ·
                    refine ⟨1466387098856104397766521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3910365596949611727377389 1466387098856104397766521)
                    ·
                      refine ⟨1099790324142078298324891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466387098856104397766521 1099790324142078298324891)
                      ·
                        rfl

theorem cell23_2141834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_2141834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141834 prefixEnd_2141834 := by exact prefixLift 2141834
  have htrace : WordTrace (prefixWord ++ tailWord_2141834) baseStart_2141834 baseEnd_2141834 := by
    simpa [prefixWord, tailWord_2141834, baseEnd_2141834] using wordTrace_append hprefix tailTrace_2141834
  have hstable : (prefixWord ++ tailWord_2141834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141834).length < 2 ^ (prefixWord ++ tailWord_2141834).sum := by decide
  have hdescent : baseEnd_2141834 < baseStart_2141834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141844 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2141844 : Nat := 118140960795 + 2141844 * 2 ^ 59
def prefixEnd_2141844 : Nat := 4983230072969 + 3 ^ 40 * 2141844 * 2
def baseEnd_2141844 : Nat := 366598486316207753066615

theorem tailTrace_2141844 : CollatzResearch.WordTrace tailWord_2141844 prefixEnd_2141844 366598486316207753066615 := by
  unfold tailWord_2141844
  simp only [CollatzResearch.WordTrace]
  refine ⟨39059734226236230338828293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52079645634981640451771057 39059734226236230338828293)
  ·
    refine ⟨7323700167419293188530305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39059734226236230338828293 7323700167419293188530305)
    ·
      refine ⟨5492775125564469891397729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7323700167419293188530305 5492775125564469891397729)
      ·
        refine ⟨4119581344173352418548297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5492775125564469891397729 4119581344173352418548297)
        ·
          refine ⟨3089686008130014313911223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4119581344173352418548297 3089686008130014313911223)
          ·
            refine ⟨4634529012195021470866835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089686008130014313911223 4634529012195021470866835)
            ·
              refine ⟨6951793518292532206300253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4634529012195021470866835 6951793518292532206300253)
              ·
                refine ⟨2606922569359699577362595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6951793518292532206300253 2606922569359699577362595)
                ·
                  refine ⟨3910383854039549366043893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606922569359699577362595 3910383854039549366043893)
                  ·
                    refine ⟨366598486316207753066615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3910383854039549366043893 366598486316207753066615)
                    ·
                      rfl

theorem cell23_2141844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2141844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141844 prefixEnd_2141844 := by exact prefixLift 2141844
  have htrace : WordTrace (prefixWord ++ tailWord_2141844) baseStart_2141844 baseEnd_2141844 := by
    simpa [prefixWord, tailWord_2141844, baseEnd_2141844] using wordTrace_append hprefix tailTrace_2141844
  have hstable : (prefixWord ++ tailWord_2141844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141844).length < 2 ^ (prefixWord ++ tailWord_2141844).sum := by decide
  have hdescent : baseEnd_2141844 < baseStart_2141844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141847 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_2141847 : Nat := 118140960795 + 2141847 * 2 ^ 59
def prefixEnd_2141847 : Nat := 4983230072969 + 3 ^ 40 * 2141847 * 2
def baseEnd_2141847 : Nat := 1099796999390586747462331

theorem tailTrace_2141847 : CollatzResearch.WordTrace tailWord_2141847 prefixEnd_2141847 1099796999390586747462331 := by
  unfold tailWord_2141847
  simp only [CollatzResearch.WordTrace]
  refine ⟨78119577871461592190015795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52079718580974394793343863 78119577871461592190015795)
  ·
    refine ⟨117179366807192388285023693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78119577871461592190015795 117179366807192388285023693)
    ·
      refine ⟨43942262552697145606883885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117179366807192388285023693 43942262552697145606883885)
      ·
        refine ⟨16478348457261429602581457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43942262552697145606883885 16478348457261429602581457)
        ·
          refine ⟨12358761342946072201936093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16478348457261429602581457 12358761342946072201936093)
          ·
            refine ⟨4634535503604777075726035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12358761342946072201936093 4634535503604777075726035)
            ·
              refine ⟨6951803255407165613589053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4634535503604777075726035 6951803255407165613589053)
              ·
                refine ⟨2606926220777687105095895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6951803255407165613589053 2606926220777687105095895)
                ·
                  refine ⟨3910389331166530657643843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606926220777687105095895 3910389331166530657643843)
                  ·
                    refine ⟨5865583996749795986465765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3910389331166530657643843 5865583996749795986465765)
                    ·
                      refine ⟨1099796999390586747462331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5865583996749795986465765 1099796999390586747462331)
                      ·
                        rfl

theorem cell23_2141847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_2141847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141847 prefixEnd_2141847 := by exact prefixLift 2141847
  have htrace : WordTrace (prefixWord ++ tailWord_2141847) baseStart_2141847 baseEnd_2141847 := by
    simpa [prefixWord, tailWord_2141847, baseEnd_2141847] using wordTrace_append hprefix tailTrace_2141847
  have hstable : (prefixWord ++ tailWord_2141847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141847).length < 2 ^ (prefixWord ++ tailWord_2141847).sum := by decide
  have hdescent : baseEnd_2141847 < baseStart_2141847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141857 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 4, 4]
def baseStart_2141857 : Nat := 118140960795 + 2141857 * 2 ^ 59
def prefixEnd_2141857 : Nat := 4983230072969 + 3 ^ 40 * 2141857 * 2
def baseEnd_2141857 : Nat := 366600711399043902779095

theorem tailTrace_2141857 : CollatzResearch.WordTrace tailWord_2141857 prefixEnd_2141857 366600711399043902779095 := by
  unfold tailWord_2141857
  simp only [CollatzResearch.WordTrace]
  refine ⟨78119942601425363897879825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52079961734283575931919883 78119942601425363897879825)
  ·
    refine ⟨58589956951069022923409869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78119942601425363897879825 58589956951069022923409869)
    ·
      refine ⟨21971233856650883596278701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58589956951069022923409869 21971233856650883596278701)
      ·
        refine ⟨8239212696244081348604513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21971233856650883596278701 8239212696244081348604513)
        ·
          refine ⟨6179409522183061011453385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8239212696244081348604513 6179409522183061011453385)
          ·
            refine ⟨4634557141637295758590039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6179409522183061011453385 4634557141637295758590039)
            ·
              refine ⟨6951835712455943637885059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4634557141637295758590039 6951835712455943637885059)
              ·
                refine ⟨10427753568683915456827589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6951835712455943637885059 10427753568683915456827589)
                ·
                  refine ⟨1955203794128234148155173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10427753568683915456827589 1955203794128234148155173)
                  ·
                    refine ⟨366600711399043902779095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1955203794128234148155173 366600711399043902779095)
                    ·
                      rfl

theorem cell23_2141857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_2141857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141857 prefixEnd_2141857 := by exact prefixLift 2141857
  have htrace : WordTrace (prefixWord ++ tailWord_2141857) baseStart_2141857 baseEnd_2141857 := by
    simpa [prefixWord, tailWord_2141857, baseEnd_2141857] using wordTrace_append hprefix tailTrace_2141857
  have hstable : (prefixWord ++ tailWord_2141857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141857).length < 2 ^ (prefixWord ++ tailWord_2141857).sum := by decide
  have hdescent : baseEnd_2141857 < baseStart_2141857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141877 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2141877 : Nat := 118140960795 + 2141877 * 2 ^ 59
def prefixEnd_2141877 : Nat := 4983230072969 + 3 ^ 40 * 2141877 * 2
def baseEnd_2141877 : Nat := 1099812403810221630087193

theorem tailTrace_2141877 : CollatzResearch.WordTrace tailWord_2141877 prefixEnd_2141877 1099812403810221630087193 := by
  unfold tailWord_2141877
  simp only [CollatzResearch.WordTrace]
  refine ⟨78120672061352907313607885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52080448040901938209071923 78120672061352907313607885)
  ·
    refine ⟨29295252023007340242602957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78120672061352907313607885 29295252023007340242602957)
    ·
      refine ⟨10985719508627752590976109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29295252023007340242602957 10985719508627752590976109)
      ·
        refine ⟨4119644815735407221616041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10985719508627752590976109 4119644815735407221616041)
        ·
          refine ⟨3089733611801555416212031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4119644815735407221616041 3089733611801555416212031)
          ·
            refine ⟨4634600417702333124318047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3089733611801555416212031 4634600417702333124318047)
            ·
              refine ⟨6951900626553499686477071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4634600417702333124318047 6951900626553499686477071)
              ·
                refine ⟨10427850939830249529715607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6951900626553499686477071 10427850939830249529715607)
                ·
                  refine ⟨15641776409745374294573411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10427850939830249529715607 15641776409745374294573411)
                  ·
                    refine ⟨23462664614618061441860117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15641776409745374294573411 23462664614618061441860117)
                    ·
                      refine ⟨1099812403810221630087193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23462664614618061441860117 1099812403810221630087193)
                      ·
                        rfl

theorem cell23_2141877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2141877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141877 prefixEnd_2141877 := by exact prefixLift 2141877
  have htrace : WordTrace (prefixWord ++ tailWord_2141877) baseStart_2141877 baseEnd_2141877 := by
    simpa [prefixWord, tailWord_2141877, baseEnd_2141877] using wordTrace_append hprefix tailTrace_2141877
  have hstable : (prefixWord ++ tailWord_2141877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141877).length < 2 ^ (prefixWord ++ tailWord_2141877).sum := by decide
  have hdescent : baseEnd_2141877 < baseStart_2141877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141883 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 2, 7]
def baseStart_2141883 : Nat := 118140960795 + 2141883 * 2 ^ 59
def prefixEnd_2141883 : Nat := 4983230072969 + 3 ^ 40 * 2141883 * 2
def baseEnd_2141883 : Nat := 366605161564716202204055

theorem tailTrace_2141883 : CollatzResearch.WordTrace tailWord_2141883 prefixEnd_2141883 366605161564716202204055 := by
  unfold tailWord_2141883
  simp only [CollatzResearch.WordTrace]
  refine ⟨78120890899331170338326303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52080593932887446892217535 78120890899331170338326303)
  ·
    refine ⟨117181336348996755507489455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78120890899331170338326303 117181336348996755507489455)
    ·
      refine ⟨175772004523495133261234183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117181336348996755507489455 175772004523495133261234183)
      ·
        refine ⟨263658006785242699891851275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175772004523495133261234183 263658006785242699891851275)
        ·
          refine ⟨395487010177864049837776913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263658006785242699891851275 395487010177864049837776913)
          ·
            refine ⟨296615257633398037378332685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395487010177864049837776913 296615257633398037378332685)
            ·
              refine ⟨111230721612524264016874757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296615257633398037378332685 111230721612524264016874757)
              ·
                refine ⟨20855760302348299503164017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111230721612524264016874757 20855760302348299503164017)
                ·
                  refine ⟨15641820226761224627373013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20855760302348299503164017 15641820226761224627373013)
                  ·
                    refine ⟨366605161564716202204055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15641820226761224627373013 366605161564716202204055)
                    ·
                      rfl

theorem cell23_2141883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_2141883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141883 prefixEnd_2141883 := by exact prefixLift 2141883
  have htrace : WordTrace (prefixWord ++ tailWord_2141883) baseStart_2141883 baseEnd_2141883 := by
    simpa [prefixWord, tailWord_2141883, baseEnd_2141883] using wordTrace_append hprefix tailTrace_2141883
  have hstable : (prefixWord ++ tailWord_2141883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141883).length < 2 ^ (prefixWord ++ tailWord_2141883).sum := by decide
  have hdescent : baseEnd_2141883 < baseStart_2141883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141884 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_2141884 : Nat := 118140960795 + 2141884 * 2 ^ 59
def prefixEnd_2141884 : Nat := 4983230072969 + 3 ^ 40 * 2141884 * 2
def baseEnd_2141884 : Nat := 1099815998174803102699661

theorem tailTrace_2141884 : CollatzResearch.WordTrace tailWord_2141884 prefixEnd_2141884 1099815998174803102699661 := by
  unfold tailWord_2141884
  simp only [CollatzResearch.WordTrace]
  refine ⟨39060463686163773754556353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52080618248218365006075137 39060463686163773754556353)
  ·
    refine ⟨29295347764622830315917265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39060463686163773754556353 29295347764622830315917265)
    ·
      refine ⟨21971510823467122736937949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29295347764622830315917265 21971510823467122736937949)
      ·
        refine ⟨8239316558800171026351731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21971510823467122736937949 8239316558800171026351731)
        ·
          refine ⟨12358974838200256539527597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8239316558800171026351731 12358974838200256539527597)
          ·
            refine ⟨4634615564325096202322849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12358974838200256539527597 4634615564325096202322849)
            ·
              refine ⟨3475961673243822151742137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4634615564325096202322849 3475961673243822151742137)
              ·
                refine ⟨2606971254932866613806603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3475961673243822151742137 2606971254932866613806603)
                ·
                  refine ⟨3910456882399299920709905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606971254932866613806603 3910456882399299920709905)
                  ·
                    refine ⟨2932842661799474940532429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3910456882399299920709905 2932842661799474940532429)
                    ·
                      refine ⟨1099815998174803102699661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932842661799474940532429 1099815998174803102699661)
                      ·
                        rfl

theorem cell23_2141884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_2141884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141884 prefixEnd_2141884 := by exact prefixLift 2141884
  have htrace : WordTrace (prefixWord ++ tailWord_2141884) baseStart_2141884 baseEnd_2141884 := by
    simpa [prefixWord, tailWord_2141884, baseEnd_2141884] using wordTrace_append hprefix tailTrace_2141884
  have hstable : (prefixWord ++ tailWord_2141884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141884).length < 2 ^ (prefixWord ++ tailWord_2141884).sum := by decide
  have hdescent : baseEnd_2141884 < baseStart_2141884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141901 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2141901 : Nat := 118140960795 + 2141901 * 2 ^ 59
def prefixEnd_2141901 : Nat := 4983230072969 + 3 ^ 40 * 2141901 * 2
def baseEnd_2141901 : Nat := 1099824727345929536187083

theorem tailTrace_2141901 : CollatzResearch.WordTrace tailWord_2141901 prefixEnd_2141901 1099824727345929536187083 := by
  unfold tailWord_2141901
  simp only [CollatzResearch.WordTrace]
  refine ⟨78121547413265959412481557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52081031608843972941654371 78121547413265959412481557)
  ·
    refine ⟨3661947534996841847460073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78121547413265959412481557 3661947534996841847460073)
    ·
      refine ⟨2746460651247631385595055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3661947534996841847460073 2746460651247631385595055)
      ·
        refine ⟨4119690976871447078392583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2746460651247631385595055 4119690976871447078392583)
        ·
          refine ⟨6179536465307170617588875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119690976871447078392583 6179536465307170617588875)
          ·
            refine ⟨9269304697960755926383313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6179536465307170617588875 9269304697960755926383313)
            ·
              refine ⟨6951978523470566944787485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9269304697960755926383313 6951978523470566944787485)
              ·
                refine ⟨2606991946301462604295307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6951978523470566944787485 2606991946301462604295307)
                ·
                  refine ⟨3910487919452193906442961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2606991946301462604295307 3910487919452193906442961)
                  ·
                    refine ⟨2932865939589145429832221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3910487919452193906442961 2932865939589145429832221)
                    ·
                      refine ⟨1099824727345929536187083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2932865939589145429832221 1099824727345929536187083)
                      ·
                        rfl

theorem cell23_2141901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2141901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141901 prefixEnd_2141901 := by exact prefixLift 2141901
  have htrace : WordTrace (prefixWord ++ tailWord_2141901) baseStart_2141901 baseEnd_2141901 := by
    simpa [prefixWord, tailWord_2141901, baseEnd_2141901] using wordTrace_append hprefix tailTrace_2141901
  have hstable : (prefixWord ++ tailWord_2141901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141901).length < 2 ^ (prefixWord ++ tailWord_2141901).sum := by decide
  have hdescent : baseEnd_2141901 < baseStart_2141901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141903 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_2141903 : Nat := 118140960795 + 2141903 * 2 ^ 59
def prefixEnd_2141903 : Nat := 4983230072969 + 3 ^ 40 * 2141903 * 2
def baseEnd_2141903 : Nat := 1099825754307238528362073

theorem tailTrace_2141903 : CollatzResearch.WordTrace tailWord_2141903 prefixEnd_2141903 1099825754307238528362073 := by
  unfold tailWord_2141903
  simp only [CollatzResearch.WordTrace]
  refine ⟨78121620359258713754054363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52081080239505809169369575 78121620359258713754054363)
  ·
    refine ⟨117182430538888070631081545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78121620359258713754054363 117182430538888070631081545)
    ·
      refine ⟨87886822904166052973311159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117182430538888070631081545 87886822904166052973311159)
      ·
        refine ⟨131830234356249079459966739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87886822904166052973311159 131830234356249079459966739)
        ·
          refine ⟨197745351534373619189950109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131830234356249079459966739 197745351534373619189950109)
          ·
            refine ⟨74154506825390107196231291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197745351534373619189950109 74154506825390107196231291)
            ·
              refine ⟨111231760238085160794346937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74154506825390107196231291 111231760238085160794346937)
              ·
                refine ⟨83423820178563870595760203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111231760238085160794346937 83423820178563870595760203)
                ·
                  refine ⟨125135730267845805893640305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83423820178563870595760203 125135730267845805893640305)
                  ·
                    refine ⟨93851797700884354420230229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125135730267845805893640305 93851797700884354420230229)
                    ·
                      refine ⟨1099825754307238528362073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 93851797700884354420230229 1099825754307238528362073)
                      ·
                        rfl

theorem cell23_2141903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_2141903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141903 prefixEnd_2141903 := by exact prefixLift 2141903
  have htrace : WordTrace (prefixWord ++ tailWord_2141903) baseStart_2141903 baseEnd_2141903 := by
    simpa [prefixWord, tailWord_2141903, baseEnd_2141903] using wordTrace_append hprefix tailTrace_2141903
  have hstable : (prefixWord ++ tailWord_2141903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141903).length < 2 ^ (prefixWord ++ tailWord_2141903).sum := by decide
  have hdescent : baseEnd_2141903 < baseStart_2141903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2141930 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_2141930 : Nat := 118140960795 + 2141930 * 2 ^ 59
def prefixEnd_2141930 : Nat := 4983230072969 + 3 ^ 40 * 2141930 * 2
def baseEnd_2141930 : Nat := 366613206094969974241483

theorem tailTrace_2141930 : CollatzResearch.WordTrace tailWord_2141930 prefixEnd_2141930 366613206094969974241483 := by
  unfold tailWord_2141930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19530651282540224341321811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52081736753440598243524829 19530651282540224341321811)
  ·
    refine ⟨29295976923810336511982717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19530651282540224341321811 29295976923810336511982717)
    ·
      refine ⟨10985991346428876191993519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29295976923810336511982717 10985991346428876191993519)
      ·
        refine ⟨16478987019643314287990279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10985991346428876191993519 16478987019643314287990279)
        ·
          refine ⟨24718480529464971431985419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16478987019643314287990279 24718480529464971431985419)
          ·
            refine ⟨37077720794197457147978129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24718480529464971431985419 37077720794197457147978129)
            ·
              refine ⟨27808290595648092860983597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37077720794197457147978129 27808290595648092860983597)
              ·
                refine ⟨10428108973368034822868849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27808290595648092860983597 10428108973368034822868849)
                ·
                  refine ⟨7821081730026026117151637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10428108973368034822868849 7821081730026026117151637)
                  ·
                    refine ⟨366613206094969974241483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7821081730026026117151637 366613206094969974241483)
                    ·
                      rfl

theorem cell23_2141930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_2141930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2141930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2141930 prefixEnd_2141930 := by exact prefixLift 2141930
  have htrace : WordTrace (prefixWord ++ tailWord_2141930) baseStart_2141930 baseEnd_2141930 := by
    simpa [prefixWord, tailWord_2141930, baseEnd_2141930] using wordTrace_append hprefix tailTrace_2141930
  have hstable : (prefixWord ++ tailWord_2141930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2141930).length < 2 ^ (prefixWord ++ tailWord_2141930).sum := by decide
  have hdescent : baseEnd_2141930 < baseStart_2141930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2141930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142022 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2142022 : Nat := 118140960795 + 2142022 * 2 ^ 59
def prefixEnd_2142022 : Nat := 4983230072969 + 3 ^ 40 * 2142022 * 2
def baseEnd_2142022 : Nat := 1099886858505123562774027

theorem tailTrace_2142022 : CollatzResearch.WordTrace tailWord_2142022 prefixEnd_2142022 1099886858505123562774027 := by
  unfold tailWord_2142022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441436270182112408676135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52083973763885064718424213 2441436270182112408676135)
  ·
    refine ⟨3662154405273168613014203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2441436270182112408676135 3662154405273168613014203)
    ·
      refine ⟨5493231607909752919521305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3662154405273168613014203 5493231607909752919521305)
      ·
        refine ⟨4119923705932314689640979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5493231607909752919521305 4119923705932314689640979)
        ·
          refine ⟨6179885558898472034461469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119923705932314689640979 6179885558898472034461469)
          ·
            refine ⟨2317457084586927012923051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6179885558898472034461469 2317457084586927012923051)
            ·
              refine ⟨3476185626880390519384577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317457084586927012923051 3476185626880390519384577)
              ·
                refine ⟨2607139220160292889538433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3476185626880390519384577 2607139220160292889538433)
                ·
                  refine ⟨1955354415120219667153825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2607139220160292889538433 1955354415120219667153825)
                  ·
                    refine ⟨1466515811340164750365369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1955354415120219667153825 1466515811340164750365369)
                    ·
                      refine ⟨1099886858505123562774027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466515811340164750365369 1099886858505123562774027)
                      ·
                        rfl

theorem cell23_2142022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2142022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142022 prefixEnd_2142022 := by exact prefixLift 2142022
  have htrace : WordTrace (prefixWord ++ tailWord_2142022) baseStart_2142022 baseEnd_2142022 := by
    simpa [prefixWord, tailWord_2142022, baseEnd_2142022] using wordTrace_append hprefix tailTrace_2142022
  have hstable : (prefixWord ++ tailWord_2142022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142022).length < 2 ^ (prefixWord ++ tailWord_2142022).sum := by decide
  have hdescent : baseEnd_2142022 < baseStart_2142022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142047 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 3]
def baseStart_2142047 : Nat := 118140960795 + 2142047 * 2 ^ 59
def prefixEnd_2142047 : Nat := 4983230072969 + 3 ^ 40 * 2142047 * 2
def baseEnd_2142047 : Nat := 1099899695521485964961411

theorem tailTrace_2142047 : CollatzResearch.WordTrace tailWord_2142047 prefixEnd_2142047 1099899695521485964961411 := by
  unfold tailWord_2142047
  simp only [CollatzResearch.WordTrace]
  refine ⟨78126872470737026347296395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52084581647158017564864263 78126872470737026347296395)
  ·
    refine ⟨117190308706105539520944593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78126872470737026347296395 117190308706105539520944593)
    ·
      refine ⟨87892731529579154640708445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117190308706105539520944593 87892731529579154640708445)
      ·
        refine ⟨32959774323592182990265667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87892731529579154640708445 32959774323592182990265667)
        ·
          refine ⟨49439661485388274485398501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32959774323592182990265667 49439661485388274485398501)
          ·
            refine ⟨9269936528510301466012219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49439661485388274485398501 9269936528510301466012219)
            ·
              refine ⟨13904904792765452199018329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9269936528510301466012219 13904904792765452199018329)
              ·
                refine ⟨10428678594574089149263747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13904904792765452199018329 10428678594574089149263747)
                ·
                  refine ⟨15643017891861133723895621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10428678594574089149263747 15643017891861133723895621)
                  ·
                    refine ⟨2933065854723962573230429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15643017891861133723895621 2933065854723962573230429)
                    ·
                      refine ⟨1099899695521485964961411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933065854723962573230429 1099899695521485964961411)
                      ·
                        rfl

theorem cell23_2142047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_2142047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142047 prefixEnd_2142047 := by exact prefixLift 2142047
  have htrace : WordTrace (prefixWord ++ tailWord_2142047) baseStart_2142047 baseEnd_2142047 := by
    simpa [prefixWord, tailWord_2142047, baseEnd_2142047] using wordTrace_append hprefix tailTrace_2142047
  have hstable : (prefixWord ++ tailWord_2142047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142047).length < 2 ^ (prefixWord ++ tailWord_2142047).sum := by decide
  have hdescent : baseEnd_2142047 < baseStart_2142047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142088 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 3, 4]
def baseStart_2142088 : Nat := 118140960795 + 2142088 * 2 ^ 59
def prefixEnd_2142088 : Nat := 4983230072969 + 3 ^ 40 * 2142088 * 2
def baseEnd_2142088 : Nat := 366640249409440101516241

theorem tailTrace_2142088 : CollatzResearch.WordTrace tailWord_2142088 prefixEnd_2142088 366640249409440101516241 := by
  unfold tailWord_2142088
  simp only [CollatzResearch.WordTrace]
  refine ⟨39064183931794245174769459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52085578575725660233025945 39064183931794245174769459)
  ·
    refine ⟨58596275897691367762154189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39064183931794245174769459 58596275897691367762154189)
    ·
      refine ⟨21973603461634262910807821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58596275897691367762154189 21973603461634262910807821)
      ·
        refine ⟨8240101298112848591552933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21973603461634262910807821 8240101298112848591552933)
        ·
          refine ⟨1545018993396159110916175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8240101298112848591552933 1545018993396159110916175)
          ·
            refine ⟨2317528490094238666374263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545018993396159110916175 2317528490094238666374263)
            ·
              refine ⟨3476292735141357999561395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317528490094238666374263 3476292735141357999561395)
              ·
                refine ⟨5214439102712036999342093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476292735141357999561395 5214439102712036999342093)
                ·
                  refine ⟨1955414663517013874753285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5214439102712036999342093 1955414663517013874753285)
                  ·
                    refine ⟨366640249409440101516241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1955414663517013874753285 366640249409440101516241)
                    ·
                      rfl

theorem cell23_2142088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_2142088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142088 prefixEnd_2142088 := by exact prefixLift 2142088
  have htrace : WordTrace (prefixWord ++ tailWord_2142088) baseStart_2142088 baseEnd_2142088 := by
    simpa [prefixWord, tailWord_2142088, baseEnd_2142088] using wordTrace_append hprefix tailTrace_2142088
  have hstable : (prefixWord ++ tailWord_2142088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142088).length < 2 ^ (prefixWord ++ tailWord_2142088).sum := by decide
  have hdescent : baseEnd_2142088 < baseStart_2142088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142127 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 1, 6]
def baseStart_2142127 : Nat := 118140960795 + 2142127 * 2 ^ 59
def prefixEnd_2142127 : Nat := 4983230072969 + 3 ^ 40 * 2142127 * 2
def baseEnd_2142127 : Nat := 366646924657948550653681

theorem tailTrace_2142127 : CollatzResearch.WordTrace tailWord_2142127 prefixEnd_2142127 366646924657948550653681 := by
  unfold tailWord_2142127
  simp only [CollatzResearch.WordTrace]
  refine ⟨78129790310447200010208635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52086526873631466673472423 78129790310447200010208635)
  ·
    refine ⟨117194685465670800015312953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78129790310447200010208635 117194685465670800015312953)
    ·
      refine ⟨87896014099253100011484715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117194685465670800015312953 87896014099253100011484715)
      ·
        refine ⟨131844021148879650017227073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87896014099253100011484715 131844021148879650017227073)
        ·
          refine ⟨98883015861659737512920305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131844021148879650017227073 98883015861659737512920305)
          ·
            refine ⟨74162261896244803134690229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98883015861659737512920305 74162261896244803134690229)
            ·
              refine ⟨6952712052772950293877209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74162261896244803134690229 6952712052772950293877209)
              ·
                refine ⟨5214534039579712720407907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6952712052772950293877209 5214534039579712720407907)
                ·
                  refine ⟨7821801059369569080611861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5214534039579712720407907 7821801059369569080611861)
                  ·
                    refine ⟨366646924657948550653681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7821801059369569080611861 366646924657948550653681)
                    ·
                      rfl

theorem cell23_2142127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_2142127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142127 prefixEnd_2142127 := by exact prefixLift 2142127
  have htrace : WordTrace (prefixWord ++ tailWord_2142127) baseStart_2142127 baseEnd_2142127 := by
    simpa [prefixWord, tailWord_2142127, baseEnd_2142127] using wordTrace_append hprefix tailTrace_2142127
  have hstable : (prefixWord ++ tailWord_2142127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142127).length < 2 ^ (prefixWord ++ tailWord_2142127).sum := by decide
  have hdescent : baseEnd_2142127 < baseStart_2142127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142151 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_2142151 : Nat := 118140960795 + 2142151 * 2 ^ 59
def prefixEnd_2142151 : Nat := 4983230072969 + 3 ^ 40 * 2142151 * 2
def baseEnd_2142151 : Nat := 1099953097509553558060933

theorem tailTrace_2142151 : CollatzResearch.WordTrace tailWord_2142151 prefixEnd_2142151 1099953097509553558060933 := by
  unfold tailWord_2142151
  simp only [CollatzResearch.WordTrace]
  refine ⟨78130665662360252109082307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52087110441573501406054871 78130665662360252109082307)
  ·
    refine ⟨117195998493540378163623461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78130665662360252109082307 117195998493540378163623461)
    ·
      refine ⟨21974249717538820905679399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117195998493540378163623461 21974249717538820905679399)
      ·
        refine ⟨32961374576308231358519099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21974249717538820905679399 32961374576308231358519099)
        ·
          refine ⟨49442061864462347037778649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32961374576308231358519099 49442061864462347037778649)
          ·
            refine ⟨37081546398346760278333987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49442061864462347037778649 37081546398346760278333987)
            ·
              refine ⟨55622319597520140417500981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37081546398346760278333987 55622319597520140417500981)
              ·
                refine ⟨5214592462267513164140717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55622319597520140417500981 5214592462267513164140717)
                ·
                  refine ⟨1955472173350317436552769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5214592462267513164140717 1955472173350317436552769)
                  ·
                    refine ⟨1466604130012738077414577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1955472173350317436552769 1466604130012738077414577)
                    ·
                      refine ⟨1099953097509553558060933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466604130012738077414577 1099953097509553558060933)
                      ·
                        rfl

theorem cell23_2142151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_2142151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142151 prefixEnd_2142151 := by exact prefixLift 2142151
  have htrace : WordTrace (prefixWord ++ tailWord_2142151) baseStart_2142151 baseEnd_2142151 := by
    simpa [prefixWord, tailWord_2142151, baseEnd_2142151] using wordTrace_append hprefix tailTrace_2142151
  have hstable : (prefixWord ++ tailWord_2142151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142151).length < 2 ^ (prefixWord ++ tailWord_2142151).sum := by decide
  have hdescent : baseEnd_2142151 < baseStart_2142151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142154 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_2142154 : Nat := 118140960795 + 2142154 * 2 ^ 59
def prefixEnd_2142154 : Nat := 4983230072969 + 3 ^ 40 * 2142154 * 2
def baseEnd_2142154 : Nat := 1099954637951517046323419

theorem tailTrace_2142154 : CollatzResearch.WordTrace tailWord_2142154 prefixEnd_2142154 1099954637951517046323419 := by
  unfold tailWord_2142154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19532693770337345905360379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52087183387566255747627677 19532693770337345905360379)
  ·
    refine ⟨29299040655506018858040569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19532693770337345905360379 29299040655506018858040569)
    ·
      refine ⟨21974280491629514143530427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29299040655506018858040569 21974280491629514143530427)
      ·
        refine ⟨32961420737444271215295641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21974280491629514143530427 32961420737444271215295641)
        ·
          refine ⟨24721065553083203411471731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32961420737444271215295641 24721065553083203411471731)
          ·
            refine ⟨37081598329624805117207597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24721065553083203411471731 37081598329624805117207597)
            ·
              refine ⟨13905599373609301918952849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37081598329624805117207597 13905599373609301918952849)
              ·
                refine ⟨10429199530206976439214637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13905599373609301918952849 10429199530206976439214637)
                ·
                  refine ⟨3910949823827616164705489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10429199530206976439214637 3910949823827616164705489)
                  ·
                    refine ⟨2933212367870712123529117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3910949823827616164705489 2933212367870712123529117)
                    ·
                      refine ⟨1099954637951517046323419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933212367870712123529117 1099954637951517046323419)
                      ·
                        rfl

theorem cell23_2142154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_2142154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142154 prefixEnd_2142154 := by exact prefixLift 2142154
  have htrace : WordTrace (prefixWord ++ tailWord_2142154) baseStart_2142154 baseEnd_2142154 := by
    simpa [prefixWord, tailWord_2142154, baseEnd_2142154] using wordTrace_append hprefix tailTrace_2142154
  have hstable : (prefixWord ++ tailWord_2142154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142154).length < 2 ^ (prefixWord ++ tailWord_2142154).sum := by decide
  have hdescent : baseEnd_2142154 < baseStart_2142154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142201 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 3]
def baseStart_2142201 : Nat := 118140960795 + 2142201 * 2 ^ 59
def prefixEnd_2142201 : Nat := 4983230072969 + 3 ^ 40 * 2142201 * 2
def baseEnd_2142201 : Nat := 1099978771542278362435703

theorem tailTrace_2142201 : CollatzResearch.WordTrace tailWord_2142201 prefixEnd_2142201 1099978771542278362435703 := by
  unfold tailWord_2142201
  simp only [CollatzResearch.WordTrace]
  refine ⟨78132489312179110648402457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52088326208119407098934971 78132489312179110648402457)
  ·
    refine ⟨58599366984134332986301843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78132489312179110648402457 58599366984134332986301843)
    ·
      refine ⟨87899050476201499479452765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58599366984134332986301843 87899050476201499479452765)
      ·
        refine ⟨32962143928575562304794787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87899050476201499479452765 32962143928575562304794787)
        ·
          refine ⟨49443215892863343457192181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32962143928575562304794787 49443215892863343457192181)
          ·
            refine ⟨4635301489955938449111767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49443215892863343457192181 4635301489955938449111767)
            ·
              refine ⟨6952952234933907673667651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635301489955938449111767 6952952234933907673667651)
              ·
                refine ⟨10429428352400861510501477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6952952234933907673667651 10429428352400861510501477)
                ·
                  refine ⟨1955517816075161533219027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10429428352400861510501477 1955517816075161533219027)
                  ·
                    refine ⟨2933276724112742299828541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1955517816075161533219027 2933276724112742299828541)
                    ·
                      refine ⟨1099978771542278362435703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933276724112742299828541 1099978771542278362435703)
                      ·
                        rfl

theorem cell23_2142201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_2142201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142201 prefixEnd_2142201 := by exact prefixLift 2142201
  have htrace : WordTrace (prefixWord ++ tailWord_2142201) baseStart_2142201 baseEnd_2142201 := by
    simpa [prefixWord, tailWord_2142201, baseEnd_2142201] using wordTrace_append hprefix tailTrace_2142201
  have hstable : (prefixWord ++ tailWord_2142201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142201).length < 2 ^ (prefixWord ++ tailWord_2142201).sum := by decide
  have hdescent : baseEnd_2142201 < baseStart_2142201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142207 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_2142207 : Nat := 118140960795 + 2142207 * 2 ^ 59
def prefixEnd_2142207 : Nat := 4983230072969 + 3 ^ 40 * 2142207 * 2
def baseEnd_2142207 : Nat := 1099981852426205338960675

theorem tailTrace_2142207 : CollatzResearch.WordTrace tailWord_2142207 prefixEnd_2142207 1099981852426205338960675 := by
  unfold tailWord_2142207
  simp only [CollatzResearch.WordTrace]
  refine ⟨78132708150157373673120875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52088472100104915782080583 78132708150157373673120875)
  ·
    refine ⟨117199062225236060509681313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78132708150157373673120875 117199062225236060509681313)
    ·
      refine ⟨87899296668927045382260985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117199062225236060509681313 87899296668927045382260985)
      ·
        refine ⟨65924472501695284036695739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87899296668927045382260985 65924472501695284036695739)
        ·
          refine ⟨98886708752542926055043609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65924472501695284036695739 98886708752542926055043609)
          ·
            refine ⟨74165031564407194541282707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98886708752542926055043609 74165031564407194541282707)
            ·
              refine ⟨111247547346610791811924061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74165031564407194541282707 111247547346610791811924061)
              ·
                refine ⟨41717830254979046929471523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111247547346610791811924061 41717830254979046929471523)
                ·
                  refine ⟨62576745382468570394207285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41717830254979046929471523 62576745382468570394207285)
                  ·
                    refine ⟨5866569879606428474456933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62576745382468570394207285 5866569879606428474456933)
                    ·
                      refine ⟨1099981852426205338960675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5866569879606428474456933 1099981852426205338960675)
                      ·
                        rfl

theorem cell23_2142207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_2142207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142207 prefixEnd_2142207 := by exact prefixLift 2142207
  have htrace : WordTrace (prefixWord ++ tailWord_2142207) baseStart_2142207 baseEnd_2142207 := by
    simpa [prefixWord, tailWord_2142207, baseEnd_2142207] using wordTrace_append hprefix tailTrace_2142207
  have hstable : (prefixWord ++ tailWord_2142207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142207).length < 2 ^ (prefixWord ++ tailWord_2142207).sum := by decide
  have hdescent : baseEnd_2142207 < baseStart_2142207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142218 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2142218 : Nat := 118140960795 + 2142218 * 2 ^ 59
def prefixEnd_2142218 : Nat := 4983230072969 + 3 ^ 40 * 2142218 * 2
def baseEnd_2142218 : Nat := 1099987500713404795923125

theorem tailTrace_2142218 : CollatzResearch.WordTrace tailWord_2142218 prefixEnd_2142218 1099987500713404795923125 := by
  unfold tailWord_2142218
  simp only [CollatzResearch.WordTrace]
  refine ⟨19533277338279380637942827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52088739568745015034514205 19533277338279380637942827)
  ·
    refine ⟨29299916007419070956914241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19533277338279380637942827 29299916007419070956914241)
    ·
      refine ⟨21974937005564303217685681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29299916007419070956914241 21974937005564303217685681)
      ·
        refine ⟨16481202754173227413264261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21974937005564303217685681 16481202754173227413264261)
        ·
          refine ⟨3090225516407480139987049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16481202754173227413264261 3090225516407480139987049)
          ·
            refine ⟨2317669137305610104990287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3090225516407480139987049 2317669137305610104990287)
            ·
              refine ⟨3476503705958415157485431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2317669137305610104990287 3476503705958415157485431)
              ·
                refine ⟨5214755558937622736228147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476503705958415157485431 5214755558937622736228147)
                ·
                  refine ⟨7822133338406434104342221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5214755558937622736228147 7822133338406434104342221)
                  ·
                    refine ⟨2933300001902412789128333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7822133338406434104342221 2933300001902412789128333)
                    ·
                      refine ⟨1099987500713404795923125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933300001902412789128333 1099987500713404795923125)
                      ·
                        rfl

theorem cell23_2142218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2142218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142218 prefixEnd_2142218 := by exact prefixLift 2142218
  have htrace : WordTrace (prefixWord ++ tailWord_2142218) baseStart_2142218 baseEnd_2142218 := by
    simpa [prefixWord, tailWord_2142218, baseEnd_2142218] using wordTrace_append hprefix tailTrace_2142218
  have hstable : (prefixWord ++ tailWord_2142218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142218).length < 2 ^ (prefixWord ++ tailWord_2142218).sum := by decide
  have hdescent : baseEnd_2142218 < baseStart_2142218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142258 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_2142258 : Nat := 118140960795 + 2142258 * 2 ^ 59
def prefixEnd_2142258 : Nat := 4983230072969 + 3 ^ 40 * 2142258 * 2
def baseEnd_2142258 : Nat := 1100008039939584639422941

theorem tailTrace_2142258 : CollatzResearch.WordTrace tailWord_2142258 prefixEnd_2142258 1100008039939584639422941 := by
  unfold tailWord_2142258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19533642068243152345806857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52089712181981739588818285 19533642068243152345806857)
  ·
    refine ⟨14650231551182364259355143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19533642068243152345806857 14650231551182364259355143)
    ·
      refine ⟨21975347326773546389032715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14650231551182364259355143 21975347326773546389032715)
      ·
        refine ⟨32963020990160319583549073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21975347326773546389032715 32963020990160319583549073)
        ·
          refine ⟨24722265742620239687661805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32963020990160319583549073 24722265742620239687661805)
          ·
            refine ⟨9270849653482589882873177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24722265742620239687661805 9270849653482589882873177)
            ·
              refine ⟨6953137240111942412154883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9270849653482589882873177 6953137240111942412154883)
              ·
                refine ⟨10429705860167913618232325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6953137240111942412154883 10429705860167913618232325)
                ·
                  refine ⟨1955569848781483803418561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10429705860167913618232325 1955569848781483803418561)
                  ·
                    refine ⟨1466677386586112852563921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1955569848781483803418561 1466677386586112852563921)
                    ·
                      refine ⟨1100008039939584639422941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466677386586112852563921 1100008039939584639422941)
                      ·
                        rfl

theorem cell23_2142258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_2142258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142258 prefixEnd_2142258 := by exact prefixLift 2142258
  have htrace : WordTrace (prefixWord ++ tailWord_2142258) baseStart_2142258 baseEnd_2142258 := by
    simpa [prefixWord, tailWord_2142258, baseEnd_2142258] using wordTrace_append hprefix tailTrace_2142258
  have hstable : (prefixWord ++ tailWord_2142258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142258).length < 2 ^ (prefixWord ++ tailWord_2142258).sum := by decide
  have hdescent : baseEnd_2142258 < baseStart_2142258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142304 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2142304 : Nat := 118140960795 + 2142304 * 2 ^ 59
def prefixEnd_2142304 : Nat := 4983230072969 + 3 ^ 40 * 2142304 * 2
def baseEnd_2142304 : Nat := 1100031660049691459447729

theorem tailTrace_2142304 : CollatzResearch.WordTrace tailWord_2142304 prefixEnd_2142304 1100031660049691459447729 := by
  unfold tailWord_2142304
  simp only [CollatzResearch.WordTrace]
  refine ⟨39068123015402979619700983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52090830687203972826267977 39068123015402979619700983)
  ·
    refine ⟨58602184523104469429551475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39068123015402979619700983 58602184523104469429551475)
    ·
      refine ⟨87903276784656704144327213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58602184523104469429551475 87903276784656704144327213)
      ·
        refine ⟨32963728794246264054122705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87903276784656704144327213 32963728794246264054122705)
        ·
          refine ⟨24722796595684698040592029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32963728794246264054122705 24722796595684698040592029)
          ·
            refine ⟨9271048723381761765222011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24722796595684698040592029 9271048723381761765222011)
            ·
              refine ⟨13906573085072642647833017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9271048723381761765222011 13906573085072642647833017)
              ·
                refine ⟨10429929813804481985874763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13906573085072642647833017 10429929813804481985874763)
                ·
                  refine ⟨15644894720706722978812145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10429929813804481985874763 15644894720706722978812145)
                  ·
                    refine ⟨11733671040530042234109109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15644894720706722978812145 11733671040530042234109109)
                    ·
                      refine ⟨1100031660049691459447729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11733671040530042234109109 1100031660049691459447729)
                      ·
                        rfl

theorem cell23_2142304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2142304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142304 prefixEnd_2142304 := by exact prefixLift 2142304
  have htrace : WordTrace (prefixWord ++ tailWord_2142304) baseStart_2142304 baseEnd_2142304 := by
    simpa [prefixWord, tailWord_2142304, baseEnd_2142304] using wordTrace_append hprefix tailTrace_2142304
  have hstable : (prefixWord ++ tailWord_2142304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142304).length < 2 ^ (prefixWord ++ tailWord_2142304).sum := by decide
  have hdescent : baseEnd_2142304 < baseStart_2142304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142341 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_2142341 : Nat := 118140960795 + 2142341 * 2 ^ 59
def prefixEnd_2142341 : Nat := 4983230072969 + 3 ^ 40 * 2142341 * 2
def baseEnd_2142341 : Nat := 366683552944635938228353

theorem tailTrace_2142341 : CollatzResearch.WordTrace tailWord_2142341 prefixEnd_2142341 366683552944635938228353 := by
  unfold tailWord_2142341
  simp only [CollatzResearch.WordTrace]
  refine ⟨78137595531671914558498877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52091730354447943038999251 78137595531671914558498877)
  ·
    refine ⟨29301598324376967959437079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78137595531671914558498877 29301598324376967959437079)
    ·
      refine ⟨43952397486565451939155619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29301598324376967959437079 43952397486565451939155619)
      ·
        refine ⟨65928596229848177908733429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43952397486565451939155619 65928596229848177908733429)
        ·
          refine ⟨6180805896548266678943759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65928596229848177908733429 6180805896548266678943759)
          ·
            refine ⟨9271208844822400018415639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6180805896548266678943759 9271208844822400018415639)
            ·
              refine ⟨13906813267233600027623459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9271208844822400018415639 13906813267233600027623459)
              ·
                refine ⟨20860219900850400041435189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13906813267233600027623459 20860219900850400041435189)
                ·
                  refine ⟨1955645615704725003884549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20860219900850400041435189 1955645615704725003884549)
                  ·
                    refine ⟨366683552944635938228353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1955645615704725003884549 366683552944635938228353)
                    ·
                      rfl

theorem cell23_2142341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_2142341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142341 prefixEnd_2142341 := by exact prefixLift 2142341
  have htrace : WordTrace (prefixWord ++ tailWord_2142341) baseStart_2142341 baseEnd_2142341 := by
    simpa [prefixWord, tailWord_2142341, baseEnd_2142341] using wordTrace_append hprefix tailTrace_2142341
  have hstable : (prefixWord ++ tailWord_2142341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142341).length < 2 ^ (prefixWord ++ tailWord_2142341).sum := by decide
  have hdescent : baseEnd_2142341 < baseStart_2142341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142375 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2142375 : Nat := 118140960795 + 2142375 * 2 ^ 59
def prefixEnd_2142375 : Nat := 4983230072969 + 3 ^ 40 * 2142375 * 2
def baseEnd_2142375 : Nat := 366689372392053560553301

theorem tailTrace_2142375 : CollatzResearch.WordTrace tailWord_2142375 prefixEnd_2142375 366689372392053560553301 := by
  unfold tailWord_2142375
  simp only [CollatzResearch.WordTrace]
  refine ⟨78138835613548738365236579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52092557075699158910157719 78138835613548738365236579)
  ·
    refine ⟨117208253420323107547854869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78138835613548738365236579 117208253420323107547854869)
    ·
      refine ⟨5494136879077645666305697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117208253420323107547854869 5494136879077645666305697)
      ·
        refine ⟨4120602659308234249729273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5494136879077645666305697 4120602659308234249729273)
        ·
          refine ⟨3090451994481175687296955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4120602659308234249729273 3090451994481175687296955)
          ·
            refine ⟨4635677991721763530945433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090451994481175687296955 4635677991721763530945433)
            ·
              refine ⟨3476758493791322648209075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4635677991721763530945433 3476758493791322648209075)
              ·
                refine ⟨5215137740686983972313613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3476758493791322648209075 5215137740686983972313613)
                ·
                  refine ⟨1955676652757618989617605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5215137740686983972313613 1955676652757618989617605)
                  ·
                    refine ⟨366689372392053560553301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1955676652757618989617605 366689372392053560553301)
                    ·
                      rfl

theorem cell23_2142375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2142375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142375 prefixEnd_2142375 := by exact prefixLift 2142375
  have htrace : WordTrace (prefixWord ++ tailWord_2142375) baseStart_2142375 baseEnd_2142375 := by
    simpa [prefixWord, tailWord_2142375, baseEnd_2142375] using wordTrace_append hprefix tailTrace_2142375
  have hstable : (prefixWord ++ tailWord_2142375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142375).length < 2 ^ (prefixWord ++ tailWord_2142375).sum := by decide
  have hdescent : baseEnd_2142375 < baseStart_2142375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142394 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_2142394 : Nat := 118140960795 + 2142394 * 2 ^ 59
def prefixEnd_2142394 : Nat := 4983230072969 + 3 ^ 40 * 2142394 * 2
def baseEnd_2142394 : Nat := 1100077873308596107322315

theorem tailTrace_2142394 : CollatzResearch.WordTrace tailWord_2142394 prefixEnd_2142394 1100077873308596107322315 := by
  unfold tailWord_2142394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19534882150119976152544559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52093019066986603073452157 19534882150119976152544559)
  ·
    refine ⟨29302323225179964228816839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19534882150119976152544559 29302323225179964228816839)
    ·
      refine ⟨43953484837769946343225259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29302323225179964228816839 43953484837769946343225259)
      ·
        refine ⟨65930227256654919514837889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43953484837769946343225259 65930227256654919514837889)
        ·
          refine ⟨49447670442491189636128417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65930227256654919514837889 49447670442491189636128417)
          ·
            refine ⟨37085752831868392227096313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49447670442491189636128417 37085752831868392227096313)
            ·
              refine ⟨27814314623901294170322235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37085752831868392227096313 27814314623901294170322235)
              ·
                refine ⟨41721471935851941255483353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27814314623901294170322235 41721471935851941255483353)
                ·
                  refine ⟨31291103951888955941612515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41721471935851941255483353 31291103951888955941612515)
                  ·
                    refine ⟨46936655927833433912418773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31291103951888955941612515 46936655927833433912418773)
                    ·
                      refine ⟨1100077873308596107322315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46936655927833433912418773 1100077873308596107322315)
                      ·
                        rfl

theorem cell23_2142394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_2142394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142394 prefixEnd_2142394 := by exact prefixLift 2142394
  have htrace : WordTrace (prefixWord ++ tailWord_2142394) baseStart_2142394 baseEnd_2142394 := by
    simpa [prefixWord, tailWord_2142394, baseEnd_2142394] using wordTrace_append hprefix tailTrace_2142394
  have hstable : (prefixWord ++ tailWord_2142394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142394).length < 2 ^ (prefixWord ++ tailWord_2142394).sum := by decide
  have hdescent : baseEnd_2142394 < baseStart_2142394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142408 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_2142408 : Nat := 118140960795 + 2142408 * 2 ^ 59
def prefixEnd_2142408 : Nat := 4983230072969 + 3 ^ 40 * 2142408 * 2
def baseEnd_2142408 : Nat := 1100085062037759052547251

theorem tailTrace_2142408 : CollatzResearch.WordTrace tailWord_2142408 prefixEnd_2142408 1100085062037759052547251 := by
  unfold tailWord_2142408
  simp only [CollatzResearch.WordTrace]
  refine ⟨39070019611214592500593939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52093359481619456667458585 39070019611214592500593939)
  ·
    refine ⟨58605029416821888750890909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39070019611214592500593939 58605029416821888750890909)
    ·
      refine ⟨21976886031308208281584091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58605029416821888750890909 21976886031308208281584091)
      ·
        refine ⟨32965329046962312422376137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21976886031308208281584091 32965329046962312422376137)
        ·
          refine ⟨24723996785221734316782103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32965329046962312422376137 24723996785221734316782103)
          ·
            refine ⟨37085995177832601475173155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24723996785221734316782103 37085995177832601475173155)
            ·
              refine ⟨55628992766748902212759733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37085995177832601475173155 55628992766748902212759733)
              ·
                refine ⟨5215218071882709582446225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55628992766748902212759733 5215218071882709582446225)
                ·
                  refine ⟨3911413553912032186834669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5215218071882709582446225 3911413553912032186834669)
                  ·
                    refine ⟨1466780082717012070063001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3911413553912032186834669 1466780082717012070063001)
                    ·
                      refine ⟨1100085062037759052547251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466780082717012070063001 1100085062037759052547251)
                      ·
                        rfl

theorem cell23_2142408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_2142408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142408 prefixEnd_2142408 := by exact prefixLift 2142408
  have htrace : WordTrace (prefixWord ++ tailWord_2142408) baseStart_2142408 baseEnd_2142408 := by
    simpa [prefixWord, tailWord_2142408, baseEnd_2142408] using wordTrace_append hprefix tailTrace_2142408
  have hstable : (prefixWord ++ tailWord_2142408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142408).length < 2 ^ (prefixWord ++ tailWord_2142408).sum := by decide
  have hdescent : baseEnd_2142408 < baseStart_2142408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142418 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_2142418 : Nat := 118140960795 + 2142418 * 2 ^ 59
def prefixEnd_2142418 : Nat := 4983230072969 + 3 ^ 40 * 2142418 * 2
def baseEnd_2142418 : Nat := 366696732281434671140735

theorem tailTrace_2142418 : CollatzResearch.WordTrace tailWord_2142418 prefixEnd_2142418 366696732281434671140735 := by
  unfold tailWord_2142418
  simp only [CollatzResearch.WordTrace]
  refine ⟨19535100988098239177262977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52093602634928637806034605 19535100988098239177262977)
  ·
    refine ⟨14651325741073679382947233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19535100988098239177262977 14651325741073679382947233)
    ·
      refine ⟨10988494305805259537210425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14651325741073679382947233 10988494305805259537210425)
      ·
        refine ⟨8241370729353944652907819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10988494305805259537210425 8241370729353944652907819)
        ·
          refine ⟨12362056094030916979361729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241370729353944652907819 12362056094030916979361729)
          ·
            refine ⟨9271542070523187734521297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12362056094030916979361729 9271542070523187734521297)
            ·
              refine ⟨6953656552892390800890973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9271542070523187734521297 6953656552892390800890973)
              ·
                refine ⟨2607621207334646550334115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6953656552892390800890973 2607621207334646550334115)
                ·
                  refine ⟨3911431811001969825501173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607621207334646550334115 3911431811001969825501173)
                  ·
                    refine ⟨366696732281434671140735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3911431811001969825501173 366696732281434671140735)
                    ·
                      rfl

theorem cell23_2142418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_2142418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142418 prefixEnd_2142418 := by exact prefixLift 2142418
  have htrace : WordTrace (prefixWord ++ tailWord_2142418) baseStart_2142418 baseEnd_2142418 := by
    simpa [prefixWord, tailWord_2142418, baseEnd_2142418] using wordTrace_append hprefix tailTrace_2142418
  have hstable : (prefixWord ++ tailWord_2142418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142418).length < 2 ^ (prefixWord ++ tailWord_2142418).sum := by decide
  have hdescent : baseEnd_2142418 < baseStart_2142418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142432 : List Nat := [2, 1, 1, 3, 1, 3, 5, 2, 1, 1, 3]
def baseStart_2142432 : Nat := 118140960795 + 2142432 * 2 ^ 59
def prefixEnd_2142432 : Nat := 4983230072969 + 3 ^ 40 * 2142432 * 2
def baseEnd_2142432 : Nat := 1100097385573466958647141

theorem tailTrace_2142432 : CollatzResearch.WordTrace tailWord_2142432 prefixEnd_2142432 1100097385573466958647141 := by
  unfold tailWord_2142432
  simp only [CollatzResearch.WordTrace]
  refine ⟨39070457287171118550030775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52093943049561491400041033 39070457287171118550030775)
  ·
    refine ⟨58605685930756677825046163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39070457287171118550030775 58605685930756677825046163)
    ·
      refine ⟨87908528896135016737569245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58605685930756677825046163 87908528896135016737569245)
      ·
        refine ⟨32965698336050631276588467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87908528896135016737569245 32965698336050631276588467)
        ·
          refine ⟨49448547504075946914882701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32965698336050631276588467 49448547504075946914882701)
          ·
            refine ⟨18543205314028480093081013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49448547504075946914882701 18543205314028480093081013)
            ·
              refine ⟨1738425498190170008726345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18543205314028480093081013 1738425498190170008726345)
              ·
                refine ⟨1303819123642627506544759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738425498190170008726345 1303819123642627506544759)
                ·
                  refine ⟨1955728685463941259817139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1303819123642627506544759 1955728685463941259817139)
                  ·
                    refine ⟨2933593028195911889725709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1955728685463941259817139 2933593028195911889725709)
                    ·
                      refine ⟨1100097385573466958647141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933593028195911889725709 1100097385573466958647141)
                      ·
                        rfl

theorem cell23_2142432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_2142432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142432 prefixEnd_2142432 := by exact prefixLift 2142432
  have htrace : WordTrace (prefixWord ++ tailWord_2142432) baseStart_2142432 baseEnd_2142432 := by
    simpa [prefixWord, tailWord_2142432, baseEnd_2142432] using wordTrace_append hprefix tailTrace_2142432
  have hstable : (prefixWord ++ tailWord_2142432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142432).length < 2 ^ (prefixWord ++ tailWord_2142432).sum := by decide
  have hdescent : baseEnd_2142432 < baseStart_2142432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142441 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 3]
def baseStart_2142441 : Nat := 118140960795 + 2142441 * 2 ^ 59
def prefixEnd_2142441 : Nat := 4983230072969 + 3 ^ 40 * 2142441 * 2
def baseEnd_2142441 : Nat := 1100102006899357423434599

theorem tailTrace_2142441 : CollatzResearch.WordTrace tailWord_2142441 prefixEnd_2142441 1100102006899357423434599 := by
  unfold tailWord_2142441
  simp only [CollatzResearch.WordTrace]
  refine ⟨78141242831309631637139177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52094161887539754424759451 78141242831309631637139177)
  ·
    refine ⟨58605932123482223727854383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78141242831309631637139177 58605932123482223727854383)
    ·
      refine ⟨87908898185223335591781575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58605932123482223727854383 87908898185223335591781575)
      ·
        refine ⟨131863347277835003387672363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87908898185223335591781575 131863347277835003387672363)
        ·
          refine ⟨197795020916752505081508545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131863347277835003387672363 197795020916752505081508545)
          ·
            refine ⟨148346265687564378811131409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197795020916752505081508545 148346265687564378811131409)
            ·
              refine ⟨111259699265673284108348557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148346265687564378811131409 111259699265673284108348557)
              ·
                refine ⟨41722387224627481540630709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111259699265673284108348557 41722387224627481540630709)
                ·
                  refine ⟨3911473802308826394434129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41722387224627481540630709 3911473802308826394434129)
                  ·
                    refine ⟨2933605351731619795825597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3911473802308826394434129 2933605351731619795825597)
                    ·
                      refine ⟨1100102006899357423434599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933605351731619795825597 1100102006899357423434599)
                      ·
                        rfl

theorem cell23_2142441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_2142441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142441 prefixEnd_2142441 := by exact prefixLift 2142441
  have htrace : WordTrace (prefixWord ++ tailWord_2142441) baseStart_2142441 baseEnd_2142441 := by
    simpa [prefixWord, tailWord_2142441, baseEnd_2142441] using wordTrace_append hprefix tailTrace_2142441
  have hstable : (prefixWord ++ tailWord_2142441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142441).length < 2 ^ (prefixWord ++ tailWord_2142441).sum := by decide
  have hdescent : baseEnd_2142441 < baseStart_2142441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142451 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4]
def baseStart_2142451 : Nat := 118140960795 + 2142451 * 2 ^ 59
def prefixEnd_2142451 : Nat := 4983230072969 + 3 ^ 40 * 2142451 * 2
def baseEnd_2142451 : Nat := 1100107141705902384309553

theorem tailTrace_2142451 : CollatzResearch.WordTrace tailWord_2142451 prefixEnd_2142451 1100107141705902384309553 := by
  unfold tailWord_2142451
  simp only [CollatzResearch.WordTrace]
  refine ⟨78141607561273403345003207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52094405040848935563335471 78141607561273403345003207)
  ·
    refine ⟨117212411341910105017504811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78141607561273403345003207 117212411341910105017504811)
    ·
      refine ⟨175818617012865157526257217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117212411341910105017504811 175818617012865157526257217)
      ·
        refine ⟨131863962759648868144692913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175818617012865157526257217 131863962759648868144692913)
        ·
          refine ⟨98897972069736651108519685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131863962759648868144692913 98897972069736651108519685)
          ·
            refine ⟨18543369763075622082847441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98897972069736651108519685 18543369763075622082847441)
            ·
              refine ⟨13907527322306716562135581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18543369763075622082847441 13907527322306716562135581)
              ·
                refine ⟨5215322745865018710800843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13907527322306716562135581 5215322745865018710800843)
                ·
                  refine ⟨7822984118797528066201265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5215322745865018710800843 7822984118797528066201265)
                  ·
                    refine ⟨5867238089098146049650949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7822984118797528066201265 5867238089098146049650949)
                    ·
                      refine ⟨1100107141705902384309553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5867238089098146049650949 1100107141705902384309553)
                      ·
                        rfl

theorem cell23_2142451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_2142451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142451 prefixEnd_2142451 := by exact prefixLift 2142451
  have htrace : WordTrace (prefixWord ++ tailWord_2142451) baseStart_2142451 baseEnd_2142451 := by
    simpa [prefixWord, tailWord_2142451, baseEnd_2142451] using wordTrace_append hprefix tailTrace_2142451
  have hstable : (prefixWord ++ tailWord_2142451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142451).length < 2 ^ (prefixWord ++ tailWord_2142451).sum := by decide
  have hdescent : baseEnd_2142451 < baseStart_2142451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142458 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_2142458 : Nat := 118140960795 + 2142458 * 2 ^ 59
def prefixEnd_2142458 : Nat := 4983230072969 + 3 ^ 40 * 2142458 * 2
def baseEnd_2142458 : Nat := 1100110736070483856922021

theorem tailTrace_2142458 : CollatzResearch.WordTrace tailWord_2142458 prefixEnd_2142458 1100110736070483856922021 := by
  unfold tailWord_2142458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19535465718062010885127007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52094575248165362360338685 19535465718062010885127007)
  ·
    refine ⟨29303198577093016327690511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19535465718062010885127007 29303198577093016327690511)
    ·
      refine ⟨43954797865639524491535767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29303198577093016327690511 43954797865639524491535767)
      ·
        refine ⟨65932196798459286737303651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43954797865639524491535767 65932196798459286737303651)
        ·
          refine ⟨98898295197688930105955477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65932196798459286737303651 98898295197688930105955477)
          ·
            refine ⟨4635857587391668598716663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98898295197688930105955477 4635857587391668598716663)
            ·
              refine ⟨6953786381087502898074995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4635857587391668598716663 6953786381087502898074995)
              ·
                refine ⟨10430679571631254347112493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6953786381087502898074995 10430679571631254347112493)
                ·
                  refine ⟨3911504839361720380167185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10430679571631254347112493 3911504839361720380167185)
                  ·
                    refine ⟨2933628629521290285125389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3911504839361720380167185 2933628629521290285125389)
                    ·
                      refine ⟨1100110736070483856922021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933628629521290285125389 1100110736070483856922021)
                      ·
                        rfl

theorem cell23_2142458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_2142458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142458 prefixEnd_2142458 := by exact prefixLift 2142458
  have htrace : WordTrace (prefixWord ++ tailWord_2142458) baseStart_2142458 baseEnd_2142458 := by
    simpa [prefixWord, tailWord_2142458, baseEnd_2142458] using wordTrace_append hprefix tailTrace_2142458
  have hstable : (prefixWord ++ tailWord_2142458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142458).length < 2 ^ (prefixWord ++ tailWord_2142458).sum := by decide
  have hdescent : baseEnd_2142458 < baseStart_2142458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142475 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 1, 2, 3]
def baseStart_2142475 : Nat := 118140960795 + 2142475 * 2 ^ 59
def prefixEnd_2142475 : Nat := 4983230072969 + 3 ^ 40 * 2142475 * 2
def baseEnd_2142475 : Nat := 1100119465241610290409443

theorem tailTrace_2142475 : CollatzResearch.WordTrace tailWord_2142475 prefixEnd_2142475 1100119465241610290409443 := by
  unfold tailWord_2142475
  simp only [CollatzResearch.WordTrace]
  refine ⟨78142482913186455443876879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52094988608790970295917919 78142482913186455443876879)
  ·
    refine ⟨117213724369779683165815319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78142482913186455443876879 117213724369779683165815319)
    ·
      refine ⟨175820586554669524748722979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117213724369779683165815319 175820586554669524748722979)
      ·
        refine ⟨263730879832004287123084469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175820586554669524748722979 263730879832004287123084469)
        ·
          refine ⟨24724769984250401917789169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 263730879832004287123084469 24724769984250401917789169)
          ·
            refine ⟨18543577488187801438341877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24724769984250401917789169 18543577488187801438341877)
            ·
              refine ⟨1738460389517606384844551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18543577488187801438341877 1738460389517606384844551)
              ·
                refine ⟨2607690584276409577266827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738460389517606384844551 2607690584276409577266827)
                ·
                  refine ⟨3911535876414614365900241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607690584276409577266827 3911535876414614365900241)
                  ·
                    refine ⟨2933651907310960774425181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3911535876414614365900241 2933651907310960774425181)
                    ·
                      refine ⟨1100119465241610290409443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933651907310960774425181 1100119465241610290409443)
                      ·
                        rfl

theorem cell23_2142475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 2, 3].length) (baseStart_2142475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142475 prefixEnd_2142475 := by exact prefixLift 2142475
  have htrace : WordTrace (prefixWord ++ tailWord_2142475) baseStart_2142475 baseEnd_2142475 := by
    simpa [prefixWord, tailWord_2142475, baseEnd_2142475] using wordTrace_append hprefix tailTrace_2142475
  have hstable : (prefixWord ++ tailWord_2142475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142475).length < 2 ^ (prefixWord ++ tailWord_2142475).sum := by decide
  have hdescent : baseEnd_2142475 < baseStart_2142475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142515 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 1, 3, 2]
def baseStart_2142515 : Nat := 118140960795 + 2142515 * 2 ^ 59
def prefixEnd_2142515 : Nat := 4983230072969 + 3 ^ 40 * 2142515 * 2
def baseEnd_2142515 : Nat := 1100140004467790133909259

theorem tailTrace_2142515 : CollatzResearch.WordTrace tailWord_2142515 prefixEnd_2142515 1100140004467790133909259 := by
  unfold tailWord_2142515
  simp only [CollatzResearch.WordTrace]
  refine ⟨78143941833041542275332999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52095961222027694850221999 78143941833041542275332999)
  ·
    refine ⟨117215912749562313412999499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78143941833041542275332999 117215912749562313412999499)
    ·
      refine ⟨175823869124343470119499249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117215912749562313412999499 175823869124343470119499249)
      ·
        refine ⟨131867901843257602589624437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175823869124343470119499249 131867901843257602589624437)
        ·
          refine ⟨12362615797805400242777291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 131867901843257602589624437 12362615797805400242777291)
          ·
            refine ⟨18543923696708100364165937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12362615797805400242777291 18543923696708100364165937)
            ·
              refine ⟨13907942772531075273124453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18543923696708100364165937 13907942772531075273124453)
              ·
                refine ⟨2607739269849576613710835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13907942772531075273124453 2607739269849576613710835)
                ·
                  refine ⟨3911608904774364920566253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607739269849576613710835 3911608904774364920566253)
                  ·
                    refine ⟨1466853339290386845212345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3911608904774364920566253 1466853339290386845212345)
                    ·
                      refine ⟨1100140004467790133909259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466853339290386845212345 1100140004467790133909259)
                      ·
                        rfl

theorem cell23_2142515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 3, 2].length) (baseStart_2142515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142515 prefixEnd_2142515 := by exact prefixLift 2142515
  have htrace : WordTrace (prefixWord ++ tailWord_2142515) baseStart_2142515 baseEnd_2142515 := by
    simpa [prefixWord, tailWord_2142515, baseEnd_2142515] using wordTrace_append hprefix tailTrace_2142515
  have hstable : (prefixWord ++ tailWord_2142515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142515).length < 2 ^ (prefixWord ++ tailWord_2142515).sum := by decide
  have hdescent : baseEnd_2142515 < baseStart_2142515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142528 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 3, 4, 2]
def baseStart_2142528 : Nat := 118140960795 + 2142528 * 2 ^ 59
def prefixEnd_2142528 : Nat := 4983230072969 + 3 ^ 40 * 2142528 * 2
def baseEnd_2142528 : Nat := 1100146679716298583046699

theorem tailTrace_2142528 : CollatzResearch.WordTrace tailWord_2142528 prefixEnd_2142528 1100146679716298583046699 := by
  unfold tailWord_2142528
  simp only [CollatzResearch.WordTrace]
  refine ⟨39072207990997222747778119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52096277321329630330370825 39072207990997222747778119)
  ·
    refine ⟨58608311986495834121667179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39072207990997222747778119 58608311986495834121667179)
    ·
      refine ⟨87912467979743751182500769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58608311986495834121667179 87912467979743751182500769)
      ·
        refine ⟨65934350984807813386875577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87912467979743751182500769 65934350984807813386875577)
        ·
          refine ⟨49450763238605860040156683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65934350984807813386875577 49450763238605860040156683)
          ·
            refine ⟨74176144857908790060235025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49450763238605860040156683 74176144857908790060235025)
            ·
              refine ⟨55632108643431592545176269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74176144857908790060235025 55632108643431592545176269)
              ·
                refine ⟨20862040741286847204441101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55632108643431592545176269 20862040741286847204441101)
                ·
                  refine ⟨7823265277982567701665413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20862040741286847204441101 7823265277982567701665413)
                  ·
                    refine ⟨1466862239621731444062265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7823265277982567701665413 1466862239621731444062265)
                    ·
                      refine ⟨1100146679716298583046699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466862239621731444062265 1100146679716298583046699)
                      ·
                        rfl

theorem cell23_2142528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_2142528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142528 prefixEnd_2142528 := by exact prefixLift 2142528
  have htrace : WordTrace (prefixWord ++ tailWord_2142528) baseStart_2142528 baseEnd_2142528 := by
    simpa [prefixWord, tailWord_2142528, baseEnd_2142528] using wordTrace_append hprefix tailTrace_2142528
  have hstable : (prefixWord ++ tailWord_2142528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142528).length < 2 ^ (prefixWord ++ tailWord_2142528).sum := by decide
  have hdescent : baseEnd_2142528 < baseStart_2142528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142531 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5]
def baseStart_2142531 : Nat := 118140960795 + 2142531 * 2 ^ 59
def prefixEnd_2142531 : Nat := 4983230072969 + 3 ^ 40 * 2142531 * 2
def baseEnd_2142531 : Nat := 1100148220158262071309185

theorem tailTrace_2142531 : CollatzResearch.WordTrace tailWord_2142531 prefixEnd_2142531 1100148220158262071309185 := by
  unfold tailWord_2142531
  simp only [CollatzResearch.WordTrace]
  refine ⟨78144525400983577007915447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52096350267322384671943631 78144525400983577007915447)
  ·
    refine ⟨117216788101475365511873171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78144525400983577007915447 117216788101475365511873171)
    ·
      refine ⟨175825182152213048267809757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117216788101475365511873171 175825182152213048267809757)
      ·
        refine ⟨65934443307079893100428659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175825182152213048267809757 65934443307079893100428659)
        ·
          refine ⟨98901664960619839650642989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65934443307079893100428659 98901664960619839650642989)
          ·
            refine ⟨37088124360232439868991121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98901664960619839650642989 37088124360232439868991121)
            ·
              refine ⟨27816093270174329901743341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37088124360232439868991121 27816093270174329901743341)
              ·
                refine ⟨10431034976315373713153753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27816093270174329901743341 10431034976315373713153753)
                ·
                  refine ⟨7823276232236530284865315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10431034976315373713153753 7823276232236530284865315)
                  ·
                    refine ⟨11734914348354795427297973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7823276232236530284865315 11734914348354795427297973)
                    ·
                      refine ⟨1100148220158262071309185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11734914348354795427297973 1100148220158262071309185)
                      ·
                        rfl

theorem cell23_2142531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_2142531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142531 prefixEnd_2142531 := by exact prefixLift 2142531
  have htrace : WordTrace (prefixWord ++ tailWord_2142531) baseStart_2142531 baseEnd_2142531 := by
    simpa [prefixWord, tailWord_2142531, baseEnd_2142531] using wordTrace_append hprefix tailTrace_2142531
  have hstable : (prefixWord ++ tailWord_2142531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142531).length < 2 ^ (prefixWord ++ tailWord_2142531).sum := by decide
  have hdescent : baseEnd_2142531 < baseStart_2142531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142556 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2142556 : Nat := 118140960795 + 2142556 * 2 ^ 59
def prefixEnd_2142556 : Nat := 4983230072969 + 3 ^ 40 * 2142556 * 2
def baseEnd_2142556 : Nat := 1100161057174624473496571

theorem tailTrace_2142556 : CollatzResearch.WordTrace tailWord_2142556 prefixEnd_2142556 1100161057174624473496571 := by
  unfold tailWord_2142556
  simp only [CollatzResearch.WordTrace]
  refine ⟨39072718612946503138787761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52096958150595337518383681 39072718612946503138787761)
  ·
    refine ⟨29304538959709877354090821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39072718612946503138787761 29304538959709877354090821)
    ·
      refine ⟨5494601054945602003892029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29304538959709877354090821 5494601054945602003892029)
      ·
        refine ⟨2060475395604600751459511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5494601054945602003892029 2060475395604600751459511)
        ·
          refine ⟨3090713093406901127189267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060475395604600751459511 3090713093406901127189267)
          ·
            refine ⟨4636069640110351690783901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090713093406901127189267 4636069640110351690783901)
            ·
              refine ⟨1738526115041381884043963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4636069640110351690783901 1738526115041381884043963)
              ·
                refine ⟨2607789172562072826065945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1738526115041381884043963 2607789172562072826065945)
                ·
                  refine ⟨1955841879421554619549459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2607789172562072826065945 1955841879421554619549459)
                  ·
                    refine ⟨2933762819132331929324189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1955841879421554619549459 2933762819132331929324189)
                    ·
                      refine ⟨1100161057174624473496571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2933762819132331929324189 1100161057174624473496571)
                      ·
                        rfl

theorem cell23_2142556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2142556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142556 prefixEnd_2142556 := by exact prefixLift 2142556
  have htrace : WordTrace (prefixWord ++ tailWord_2142556) baseStart_2142556 baseEnd_2142556 := by
    simpa [prefixWord, tailWord_2142556, baseEnd_2142556] using wordTrace_append hprefix tailTrace_2142556
  have hstable : (prefixWord ++ tailWord_2142556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142556).length < 2 ^ (prefixWord ++ tailWord_2142556).sum := by decide
  have hdescent : baseEnd_2142556 < baseStart_2142556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142562 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_2142562 : Nat := 118140960795 + 2142562 * 2 ^ 59
def prefixEnd_2142562 : Nat := 4983230072969 + 3 ^ 40 * 2142562 * 2
def baseEnd_2142562 : Nat := 1100164138058551450021543

theorem tailTrace_2142562 : CollatzResearch.WordTrace tailWord_2142562 prefixEnd_2142562 1100164138058551450021543 := by
  unfold tailWord_2142562
  simp only [CollatzResearch.WordTrace]
  refine ⟨19536414015967817325573485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52097104042580846201529293 19536414015967817325573485)
  ·
    refine ⟨7326155255987931497090057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19536414015967817325573485 7326155255987931497090057)
    ·
      refine ⟨5494616441990948622817543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7326155255987931497090057 5494616441990948622817543)
      ·
        refine ⟨8241924662986422934226315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5494616441990948622817543 8241924662986422934226315)
        ·
          refine ⟨12362886994479634401339473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8241924662986422934226315 12362886994479634401339473)
          ·
            refine ⟨9272165245859725801004605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12362886994479634401339473 9272165245859725801004605)
            ·
              refine ⟨3477061967197397175376727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9272165245859725801004605 3477061967197397175376727)
              ·
                refine ⟨5215592950796095763065091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477061967197397175376727 5215592950796095763065091)
                ·
                  refine ⟨7823389426194143644597637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5215592950796095763065091 7823389426194143644597637)
                  ·
                    refine ⟨1466885517411401933362057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7823389426194143644597637 1466885517411401933362057)
                    ·
                      refine ⟨1100164138058551450021543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1466885517411401933362057 1100164138058551450021543)
                      ·
                        rfl

theorem cell23_2142562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_2142562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142562 prefixEnd_2142562 := by exact prefixLift 2142562
  have htrace : WordTrace (prefixWord ++ tailWord_2142562) baseStart_2142562 baseEnd_2142562 := by
    simpa [prefixWord, tailWord_2142562, baseEnd_2142562] using wordTrace_append hprefix tailTrace_2142562
  have hstable : (prefixWord ++ tailWord_2142562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142562).length < 2 ^ (prefixWord ++ tailWord_2142562).sum := by decide
  have hdescent : baseEnd_2142562 < baseStart_2142562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142568 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 7]
def baseStart_2142568 : Nat := 118140960795 + 2142568 * 2 ^ 59
def prefixEnd_2142568 : Nat := 4983230072969 + 3 ^ 40 * 2142568 * 2
def baseEnd_2142568 : Nat := 122240802104719825171835

theorem tailTrace_2142568 : CollatzResearch.WordTrace tailWord_2142568 prefixEnd_2142568 122240802104719825171835 := by
  unfold tailWord_2142568
  simp only [CollatzResearch.WordTrace]
  refine ⟨39072937450924766163506179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52097249934566354884674905 39072937450924766163506179)
  ·
    refine ⟨58609406176387149245259269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39072937450924766163506179 58609406176387149245259269)
    ·
      refine ⟨10989263658072590483486113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58609406176387149245259269 10989263658072590483486113)
      ·
        refine ⟨8241947743554442862614585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10989263658072590483486113 8241947743554442862614585)
        ·
          refine ⟨6181460807665832146960939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8241947743554442862614585 6181460807665832146960939)
          ·
            refine ⟨9272191211498748220441409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6181460807665832146960939 9272191211498748220441409)
            ·
              refine ⟨6954143408624061165331057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9272191211498748220441409 6954143408624061165331057)
              ·
                refine ⟨5215607556468045873998293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6954143408624061165331057 5215607556468045873998293)
                ·
                  refine ⟨122240802104719825171835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5215607556468045873998293 122240802104719825171835)
                  ·
                    rfl

theorem cell23_2142568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 7].length) (baseStart_2142568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142568 prefixEnd_2142568 := by exact prefixLift 2142568
  have htrace : WordTrace (prefixWord ++ tailWord_2142568) baseStart_2142568 baseEnd_2142568 := by
    simpa [prefixWord, tailWord_2142568, baseEnd_2142568] using wordTrace_append hprefix tailTrace_2142568
  have hstable : (prefixWord ++ tailWord_2142568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142568).length < 2 ^ (prefixWord ++ tailWord_2142568).sum := by decide
  have hdescent : baseEnd_2142568 < baseStart_2142568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142582 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2142582 : Nat := 118140960795 + 2142582 * 2 ^ 59
def prefixEnd_2142582 : Nat := 4983230072969 + 3 ^ 40 * 2142582 * 2
def baseEnd_2142582 : Nat := 1100174407671641371771451

theorem tailTrace_2142582 : CollatzResearch.WordTrace tailWord_2142582 prefixEnd_2142582 1100174407671641371771451 := by
  unfold tailWord_2142582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4884149095237425794876375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52097590349199208478681333 4884149095237425794876375)
  ·
    refine ⟨7326223642856138692314563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4884149095237425794876375 7326223642856138692314563)
    ·
      refine ⟨10989335464284208038471845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7326223642856138692314563 10989335464284208038471845)
      ·
        refine ⟨2060500399553289007213471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10989335464284208038471845 2060500399553289007213471)
        ·
          refine ⟨3090750599329933510820207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060500399553289007213471 3090750599329933510820207)
          ·
            refine ⟨4636125898994900266230311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090750599329933510820207 4636125898994900266230311)
            ·
              refine ⟨6954188848492350399345467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4636125898994900266230311 6954188848492350399345467)
              ·
                refine ⟨10431283272738525599018201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6954188848492350399345467 10431283272738525599018201)
                ·
                  refine ⟨7823462454553894199263651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10431283272738525599018201 7823462454553894199263651)
                  ·
                    refine ⟨11735193681830841298895477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7823462454553894199263651 11735193681830841298895477)
                    ·
                      refine ⟨1100174407671641371771451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11735193681830841298895477 1100174407671641371771451)
                      ·
                        rfl

theorem cell23_2142582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2142582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142582 prefixEnd_2142582 := by exact prefixLift 2142582
  have htrace : WordTrace (prefixWord ++ tailWord_2142582) baseStart_2142582 baseEnd_2142582 := by
    simpa [prefixWord, tailWord_2142582, baseEnd_2142582] using wordTrace_append hprefix tailTrace_2142582
  have hstable : (prefixWord ++ tailWord_2142582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142582).length < 2 ^ (prefixWord ++ tailWord_2142582).sum := by decide
  have hdescent : baseEnd_2142582 < baseStart_2142582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142591 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_2142591 : Nat := 118140960795 + 2142591 * 2 ^ 59
def prefixEnd_2142591 : Nat := 4983230072969 + 3 ^ 40 * 2142591 * 2
def baseEnd_2142591 : Nat := 1100179028997531836558909

theorem tailTrace_2142591 : CollatzResearch.WordTrace tailWord_2142591 prefixEnd_2142591 1100179028997531836558909 := by
  unfold tailWord_2142591
  simp only [CollatzResearch.WordTrace]
  refine ⟨78146713780766207255099627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52097809187177471503399751 78146713780766207255099627)
  ·
    refine ⟨117220070671149310882649441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78146713780766207255099627 117220070671149310882649441)
    ·
      refine ⟨87915053003361983161987081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117220070671149310882649441 87915053003361983161987081)
      ·
        refine ⟨65936289752521487371490311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87915053003361983161987081 65936289752521487371490311)
        ·
          refine ⟨98904434628782231057235467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65936289752521487371490311 98904434628782231057235467)
          ·
            refine ⟨148356651943173346585853201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98904434628782231057235467 148356651943173346585853201)
            ·
              refine ⟨111267488957380009939389901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148356651943173346585853201 111267488957380009939389901)
              ·
                refine ⟨41725308359017503727271213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111267488957380009939389901 41725308359017503727271213)
                ·
                  refine ⟨15646990634631563897726705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41725308359017503727271213 15646990634631563897726705)
                  ·
                    refine ⟨11735242975973672923295029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15646990634631563897726705 11735242975973672923295029)
                    ·
                      refine ⟨1100179028997531836558909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11735242975973672923295029 1100179028997531836558909)
                      ·
                        rfl

theorem cell23_2142591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_2142591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142591 prefixEnd_2142591 := by exact prefixLift 2142591
  have htrace : WordTrace (prefixWord ++ tailWord_2142591) baseStart_2142591 baseEnd_2142591 := by
    simpa [prefixWord, tailWord_2142591, baseEnd_2142591] using wordTrace_append hprefix tailTrace_2142591
  have hstable : (prefixWord ++ tailWord_2142591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142591).length < 2 ^ (prefixWord ++ tailWord_2142591).sum := by decide
  have hdescent : baseEnd_2142591 < baseStart_2142591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142602 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 7]
def baseStart_2142602 : Nat := 118140960795 + 2142602 * 2 ^ 59
def prefixEnd_2142602 : Nat := 4983230072969 + 3 ^ 40 * 2142602 * 2
def baseEnd_2142602 : Nat := 122242741920525699280151

theorem tailTrace_2142602 : CollatzResearch.WordTrace tailWord_2142602 prefixEnd_2142602 122242741920525699280151 := by
  unfold tailWord_2142602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19536778745931589033437515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52098076655817570755833373 19536778745931589033437515)
  ·
    refine ⟨29305168118897383550156273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19536778745931589033437515 29305168118897383550156273)
    ·
      refine ⟨21978876089173037662617205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29305168118897383550156273 21978876089173037662617205)
      ·
        refine ⟨2060519633359972280870363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21978876089173037662617205 2060519633359972280870363)
        ·
          refine ⟨3090779450039958421305545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060519633359972280870363 3090779450039958421305545)
          ·
            refine ⟨2318084587529968815979159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3090779450039958421305545 2318084587529968815979159)
            ·
              refine ⟨3477126881294953223968739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318084587529968815979159 3477126881294953223968739)
              ·
                refine ⟨5215690321942429835953109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477126881294953223968739 5215690321942429835953109)
                ·
                  refine ⟨122242741920525699280151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5215690321942429835953109 122242741920525699280151)
                  ·
                    rfl

theorem cell23_2142602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_2142602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142602 prefixEnd_2142602 := by exact prefixLift 2142602
  have htrace : WordTrace (prefixWord ++ tailWord_2142602) baseStart_2142602 baseEnd_2142602 := by
    simpa [prefixWord, tailWord_2142602, baseEnd_2142602] using wordTrace_append hprefix tailTrace_2142602
  have hstable : (prefixWord ++ tailWord_2142602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142602).length < 2 ^ (prefixWord ++ tailWord_2142602).sum := by decide
  have hdescent : baseEnd_2142602 < baseStart_2142602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142632 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2142632 : Nat := 118140960795 + 2142632 * 2 ^ 59
def prefixEnd_2142632 : Nat := 4983230072969 + 3 ^ 40 * 2142632 * 2
def baseEnd_2142632 : Nat := 366733360568122058715407

theorem tailTrace_2142632 : CollatzResearch.WordTrace tailWord_2142632 prefixEnd_2142632 366733360568122058715407 := by
  unfold tailWord_2142632
  simp only [CollatzResearch.WordTrace]
  refine ⟨39074104586808835628671075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52098806115745114171561433 39074104586808835628671075)
  ·
    refine ⟨58611156880213253443006613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39074104586808835628671075 58611156880213253443006613)
    ·
      refine ⟨2747397978759996255140935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58611156880213253443006613 2747397978759996255140935)
      ·
        refine ⟨4121096968139994382711403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747397978759996255140935 4121096968139994382711403)
        ·
          refine ⟨6181645452209991574067105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121096968139994382711403 6181645452209991574067105)
          ·
            refine ⟨4636234089157493680550329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6181645452209991574067105 4636234089157493680550329)
            ·
              refine ⟨3477175566868120260412747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4636234089157493680550329 3477175566868120260412747)
              ·
                refine ⟨5215763350302180390619121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477175566868120260412747 5215763350302180390619121)
                ·
                  refine ⟨3911822512726635292964341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5215763350302180390619121 3911822512726635292964341)
                  ·
                    refine ⟨366733360568122058715407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3911822512726635292964341 366733360568122058715407)
                    ·
                      rfl

theorem cell23_2142632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2142632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142632 prefixEnd_2142632 := by exact prefixLift 2142632
  have htrace : WordTrace (prefixWord ++ tailWord_2142632) baseStart_2142632 baseEnd_2142632 := by
    simpa [prefixWord, tailWord_2142632, baseEnd_2142632] using wordTrace_append hprefix tailTrace_2142632
  have hstable : (prefixWord ++ tailWord_2142632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142632).length < 2 ^ (prefixWord ++ tailWord_2142632).sum := by decide
  have hdescent : baseEnd_2142632 < baseStart_2142632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142651 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7]
def baseStart_2142651 : Nat := 118140960795 + 2142651 * 2 ^ 59
def prefixEnd_2142651 : Nat := 4983230072969 + 3 ^ 40 * 2142651 * 2
def baseEnd_2142651 : Nat := 1100209837836801601808633

theorem tailTrace_2142651 : CollatzResearch.WordTrace tailWord_2142651 prefixEnd_2142651 1100209837836801601808633 := by
  unfold tailWord_2142651
  simp only [CollatzResearch.WordTrace]
  refine ⟨78148902160548837502283807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52099268107032558334855871 78148902160548837502283807)
  ·
    refine ⟨117223353240823256253425711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78148902160548837502283807 117223353240823256253425711)
    ·
      refine ⟨175835029861234884380138567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117223353240823256253425711 175835029861234884380138567)
      ·
        refine ⟨263752544791852326570207851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175835029861234884380138567 263752544791852326570207851)
        ·
          refine ⟨395628817187778489855311777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263752544791852326570207851 395628817187778489855311777)
          ·
            refine ⟨296721612890833867391483833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395628817187778489855311777 296721612890833867391483833)
            ·
              refine ⟨222541209668125400543612875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296721612890833867391483833 222541209668125400543612875)
              ·
                refine ⟨333811814502188100815419313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222541209668125400543612875 333811814502188100815419313)
                ·
                  refine ⟨250358860876641075611564485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 333811814502188100815419313 250358860876641075611564485)
                  ·
                    refine ⟨46942286414370201677168341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250358860876641075611564485 46942286414370201677168341)
                    ·
                      refine ⟨1100209837836801601808633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46942286414370201677168341 1100209837836801601808633)
                      ·
                        rfl

theorem cell23_2142651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_2142651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142651 prefixEnd_2142651 := by exact prefixLift 2142651
  have htrace : WordTrace (prefixWord ++ tailWord_2142651) baseStart_2142651 baseEnd_2142651 := by
    simpa [prefixWord, tailWord_2142651, baseEnd_2142651] using wordTrace_append hprefix tailTrace_2142651
  have hstable : (prefixWord ++ tailWord_2142651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142651).length < 2 ^ (prefixWord ++ tailWord_2142651).sum := by decide
  have hdescent : baseEnd_2142651 < baseStart_2142651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142688 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 3, 5]
def baseStart_2142688 : Nat := 118140960795 + 2142688 * 2 ^ 59
def prefixEnd_2142688 : Nat := 4983230072969 + 3 ^ 40 * 2142688 * 2
def baseEnd_2142688 : Nat := 366742945540339319015321

theorem tailTrace_2142688 : CollatzResearch.WordTrace tailWord_2142688 prefixEnd_2142688 366742945540339319015321 := by
  unfold tailWord_2142688
  simp only [CollatzResearch.WordTrace]
  refine ⟨39075125830707396410690359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52100167774276528547587145 39075125830707396410690359)
  ·
    refine ⟨58612688746061094616035539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39075125830707396410690359 58612688746061094616035539)
    ·
      refine ⟨87919033119091641924053309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58612688746061094616035539 87919033119091641924053309)
      ·
        refine ⟨32969637419659365721519991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87919033119091641924053309 32969637419659365721519991)
        ·
          refine ⟨49454456129489048582279987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32969637419659365721519991 49454456129489048582279987)
          ·
            refine ⟨74181684194233572873419981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49454456129489048582279987 74181684194233572873419981)
            ·
              refine ⟨27818131572837589827532493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74181684194233572873419981 27818131572837589827532493)
              ·
                refine ⟨10431799339814096185324685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27818131572837589827532493 10431799339814096185324685)
                ·
                  refine ⟨3911924752430286069496757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10431799339814096185324685 3911924752430286069496757)
                  ·
                    refine ⟨366742945540339319015321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3911924752430286069496757 366742945540339319015321)
                    ·
                      rfl

theorem cell23_2142688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_2142688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142688 prefixEnd_2142688 := by exact prefixLift 2142688
  have htrace : WordTrace (prefixWord ++ tailWord_2142688) baseStart_2142688 baseEnd_2142688 := by
    simpa [prefixWord, tailWord_2142688, baseEnd_2142688] using wordTrace_append hprefix tailTrace_2142688
  have hstable : (prefixWord ++ tailWord_2142688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142688).length < 2 ^ (prefixWord ++ tailWord_2142688).sum := by decide
  have hdescent : baseEnd_2142688 < baseStart_2142688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142705 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 1, 5]
def baseStart_2142705 : Nat := 118140960795 + 2142705 * 2 ^ 59
def prefixEnd_2142705 : Nat := 4983230072969 + 3 ^ 40 * 2142705 * 2
def baseEnd_2142705 : Nat := 366745855264048130177795

theorem tailTrace_2142705 : CollatzResearch.WordTrace tailWord_2142705 prefixEnd_2142705 366745855264048130177795 := by
  unfold tailWord_2142705
  simp only [CollatzResearch.WordTrace]
  refine ⟨78150871702353204724749569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52100581134902136483166379 78150871702353204724749569)
  ·
    refine ⟨58613153776764903543562177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78150871702353204724749569 58613153776764903543562177)
    ·
      refine ⟨43959865332573677657671633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58613153776764903543562177 43959865332573677657671633)
      ·
        refine ⟨32969898999430258243253725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43959865332573677657671633 32969898999430258243253725)
        ·
          refine ⟨12363712124786346841220147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32969898999430258243253725 12363712124786346841220147)
          ·
            refine ⟨18545568187179520261830221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12363712124786346841220147 18545568187179520261830221)
            ·
              refine ⟨6954588070192320098186333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18545568187179520261830221 6954588070192320098186333)
              ·
                refine ⟨2607970526322120036819875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6954588070192320098186333 2607970526322120036819875)
                ·
                  refine ⟨3911955789483180055229813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2607970526322120036819875 3911955789483180055229813)
                  ·
                    refine ⟨366745855264048130177795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3911955789483180055229813 366745855264048130177795)
                    ·
                      rfl

theorem cell23_2142705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_2142705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142705 prefixEnd_2142705 := by exact prefixLift 2142705
  have htrace : WordTrace (prefixWord ++ tailWord_2142705) baseStart_2142705 baseEnd_2142705 := by
    simpa [prefixWord, tailWord_2142705, baseEnd_2142705] using wordTrace_append hprefix tailTrace_2142705
  have hstable : (prefixWord ++ tailWord_2142705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142705).length < 2 ^ (prefixWord ++ tailWord_2142705).sum := by decide
  have hdescent : baseEnd_2142705 < baseStart_2142705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142709 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 6]
def baseStart_2142709 : Nat := 118140960795 + 2142709 * 2 ^ 59
def prefixEnd_2142709 : Nat := 4983230072969 + 3 ^ 40 * 2142709 * 2
def baseEnd_2142709 : Nat := 122248846634973597209263

theorem tailTrace_2142709 : CollatzResearch.WordTrace tailWord_2142709 prefixEnd_2142709 122248846634973597209263 := by
  unfold tailWord_2142709
  simp only [CollatzResearch.WordTrace]
  refine ⟨78151017594338713407895181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52100678396225808938596787 78151017594338713407895181)
  ·
    refine ⟨29306631597877017527960693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78151017594338713407895181 29306631597877017527960693)
    ·
      refine ⟨2747496712300970393246315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29306631597877017527960693 2747496712300970393246315)
      ·
        refine ⟨4121245068451455589869473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747496712300970393246315 4121245068451455589869473)
        ·
          refine ⟨3090933801338591692402105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4121245068451455589869473 3090933801338591692402105)
          ·
            refine ⟨2318200351003943769301579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3090933801338591692402105 2318200351003943769301579)
            ·
              refine ⟨3477300526505915653952369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318200351003943769301579 3477300526505915653952369)
              ·
                refine ⟨2607975394879436740464277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3477300526505915653952369 2607975394879436740464277)
                ·
                  refine ⟨122248846634973597209263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2607975394879436740464277 122248846634973597209263)
                  ·
                    rfl

theorem cell23_2142709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_2142709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142709 prefixEnd_2142709 := by exact prefixLift 2142709
  have htrace : WordTrace (prefixWord ++ tailWord_2142709) baseStart_2142709 baseEnd_2142709 := by
    simpa [prefixWord, tailWord_2142709, baseEnd_2142709] using wordTrace_append hprefix tailTrace_2142709
  have hstable : (prefixWord ++ tailWord_2142709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142709).length < 2 ^ (prefixWord ++ tailWord_2142709).sum := by decide
  have hdescent : baseEnd_2142709 < baseStart_2142709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142762 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_2142762 : Nat := 118140960795 + 2142762 * 2 ^ 59
def prefixEnd_2142762 : Nat := 4983230072969 + 3 ^ 40 * 2142762 * 2
def baseEnd_2142762 : Nat := 1100266834189450667520623

theorem tailTrace_2142762 : CollatzResearch.WordTrace tailWord_2142762 prefixEnd_2142762 1100266834189450667520623 := by
  unfold tailWord_2142762
  simp only [CollatzResearch.WordTrace]
  refine ⟨19538237665786675864893635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52101967108764468973049693 19538237665786675864893635)
  ·
    refine ⟨29307356498680013797340453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19538237665786675864893635 29307356498680013797340453)
    ·
      refine ⟨5495129343502502587001335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29307356498680013797340453 5495129343502502587001335)
      ·
        refine ⟨8242694015253753880502003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5495129343502502587001335 8242694015253753880502003)
        ·
          refine ⟨12364041022880630820753005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8242694015253753880502003 12364041022880630820753005)
          ·
            refine ⟨4636515383580236557782377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12364041022880630820753005 4636515383580236557782377)
            ·
              refine ⟨3477386537685177418336783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4636515383580236557782377 3477386537685177418336783)
              ·
                refine ⟨5216079806527766127505175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477386537685177418336783 5216079806527766127505175)
                ·
                  refine ⟨7824119709791649191257763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5216079806527766127505175 7824119709791649191257763)
                  ·
                    refine ⟨11736179564687473786886645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7824119709791649191257763 11736179564687473786886645)
                    ·
                      refine ⟨1100266834189450667520623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11736179564687473786886645 1100266834189450667520623)
                      ·
                        rfl

theorem cell23_2142762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_2142762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142762 prefixEnd_2142762 := by exact prefixLift 2142762
  have htrace : WordTrace (prefixWord ++ tailWord_2142762) baseStart_2142762 baseEnd_2142762 := by
    simpa [prefixWord, tailWord_2142762, baseEnd_2142762] using wordTrace_append hprefix tailTrace_2142762
  have hstable : (prefixWord ++ tailWord_2142762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142762).length < 2 ^ (prefixWord ++ tailWord_2142762).sum := by decide
  have hdescent : baseEnd_2142762 < baseStart_2142762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142849 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_2142849 : Nat := 118140960795 + 2142849 * 2 ^ 59
def prefixEnd_2142849 : Nat := 4983230072969 + 3 ^ 40 * 2142849 * 2
def baseEnd_2142849 : Nat := 1100311507006391827132723

theorem tailTrace_2142849 : CollatzResearch.WordTrace tailWord_2142849 prefixEnd_2142849 1100311507006391827132723 := by
  unfold tailWord_2142849
  simp only [CollatzResearch.WordTrace]
  refine ⟨78156123813831517317991601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52104082542554344878661067 78156123813831517317991601)
  ·
    refine ⟨58617092860373637988493701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78156123813831517317991601 58617092860373637988493701)
    ·
      refine ⟨10990704911320057122842569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58617092860373637988493701 10990704911320057122842569)
      ·
        refine ⟨8243028683490042842131927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10990704911320057122842569 8243028683490042842131927)
        ·
          refine ⟨12364543025235064263197891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8243028683490042842131927 12364543025235064263197891)
          ·
            refine ⟨18546814537852596394796837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12364543025235064263197891 18546814537852596394796837)
            ·
              refine ⟨3477527725847361824024407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18546814537852596394796837 3477527725847361824024407)
              ·
                refine ⟨5216291588771042736036611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477527725847361824024407 5216291588771042736036611)
                ·
                  refine ⟨7824437383156564104054917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5216291588771042736036611 7824437383156564104054917)
                  ·
                    refine ⟨1467082009341855769510297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7824437383156564104054917 1467082009341855769510297)
                    ·
                      refine ⟨1100311507006391827132723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467082009341855769510297 1100311507006391827132723)
                      ·
                        rfl

theorem cell23_2142849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_2142849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142849 prefixEnd_2142849 := by exact prefixLift 2142849
  have htrace : WordTrace (prefixWord ++ tailWord_2142849) baseStart_2142849 baseEnd_2142849 := by
    simpa [prefixWord, tailWord_2142849, baseEnd_2142849] using wordTrace_append hprefix tailTrace_2142849
  have hstable : (prefixWord ++ tailWord_2142849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142849).length < 2 ^ (prefixWord ++ tailWord_2142849).sum := by decide
  have hdescent : baseEnd_2142849 < baseStart_2142849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142855 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 7]
def baseStart_2142855 : Nat := 118140960795 + 2142855 * 2 ^ 59
def prefixEnd_2142855 : Nat := 4983230072969 + 3 ^ 40 * 2142855 * 2
def baseEnd_2142855 : Nat := 122257176432257644850855

theorem tailTrace_2142855 : CollatzResearch.WordTrace tailWord_2142855 prefixEnd_2142855 122257176432257644850855 := by
  unfold tailWord_2142855
  simp only [CollatzResearch.WordTrace]
  refine ⟨78156342651809780342710019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52104228434539853561806679 78156342651809780342710019)
  ·
    refine ⟨117234513977714670514065029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78156342651809780342710019 117234513977714670514065029)
    ·
      refine ⟨21981471370821500721387193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117234513977714670514065029 21981471370821500721387193)
      ·
        refine ⟨16486103528116125541040395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21981471370821500721387193 16486103528116125541040395)
        ·
          refine ⟨24729155292174188311560593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16486103528116125541040395 24729155292174188311560593)
          ·
            refine ⟨18546866469130641233670445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24729155292174188311560593 18546866469130641233670445)
            ·
              refine ⟨6955074925923990462626417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18546866469130641233670445 6955074925923990462626417)
              ·
                refine ⟨5216306194442992846969813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6955074925923990462626417 5216306194442992846969813)
                ·
                  refine ⟨122257176432257644850855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5216306194442992846969813 122257176432257644850855)
                  ·
                    rfl

theorem cell23_2142855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 7].length) (baseStart_2142855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142855 prefixEnd_2142855 := by exact prefixLift 2142855
  have htrace : WordTrace (prefixWord ++ tailWord_2142855) baseStart_2142855 baseEnd_2142855 := by
    simpa [prefixWord, tailWord_2142855, baseEnd_2142855] using wordTrace_append hprefix tailTrace_2142855
  have hstable : (prefixWord ++ tailWord_2142855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142855).length < 2 ^ (prefixWord ++ tailWord_2142855).sum := by decide
  have hdescent : baseEnd_2142855 < baseStart_2142855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142885 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 4, 5]
def baseStart_2142885 : Nat := 118140960795 + 2142885 * 2 ^ 59
def prefixEnd_2142885 : Nat := 4983230072969 + 3 ^ 40 * 2142885 * 2
def baseEnd_2142885 : Nat := 366776664103317895427519

theorem tailTrace_2142885 : CollatzResearch.WordTrace tailWord_2142885 prefixEnd_2142885 366776664103317895427519 := by
  unfold tailWord_2142885
  simp only [CollatzResearch.WordTrace]
  refine ⟨78157436841701095466302109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52104957894467396977534739 78157436841701095466302109)
  ·
    refine ⟨29309038815637910799863291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78157436841701095466302109 29309038815637910799863291)
    ·
      refine ⟨43963558223456866199794937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29309038815637910799863291 43963558223456866199794937)
      ·
        refine ⟨32972668667592649649846203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43963558223456866199794937 32972668667592649649846203)
        ·
          refine ⟨49459003001388974474769305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32972668667592649649846203 49459003001388974474769305)
          ·
            refine ⟨37094252251041730856076979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49459003001388974474769305 37094252251041730856076979)
            ·
              refine ⟨55641378376562596284115469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37094252251041730856076979 55641378376562596284115469)
              ·
                refine ⟨20865516891210973606543301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55641378376562596284115469 20865516891210973606543301)
                ·
                  refine ⟨3912284417102057551226869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20865516891210973606543301 3912284417102057551226869)
                  ·
                    refine ⟨366776664103317895427519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3912284417102057551226869 366776664103317895427519)
                    ·
                      rfl

theorem cell23_2142885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_2142885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142885 prefixEnd_2142885 := by exact prefixLift 2142885
  have htrace : WordTrace (prefixWord ++ tailWord_2142885) baseStart_2142885 baseEnd_2142885 := by
    simpa [prefixWord, tailWord_2142885, baseEnd_2142885] using wordTrace_append hprefix tailTrace_2142885
  have hstable : (prefixWord ++ tailWord_2142885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142885).length < 2 ^ (prefixWord ++ tailWord_2142885).sum := by decide
  have hdescent : baseEnd_2142885 < baseStart_2142885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142922 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2142922 : Nat := 118140960795 + 2142922 * 2 ^ 59
def prefixEnd_2142922 : Nat := 4983230072969 + 3 ^ 40 * 2142922 * 2
def baseEnd_2142922 : Nat := 1100348991094170041519887

theorem tailTrace_2142922 : CollatzResearch.WordTrace tailWord_2142922 prefixEnd_2142922 1100348991094170041519887 := by
  unfold tailWord_2142922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19539696585641762696349755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52105857561711367190266013 19539696585641762696349755)
  ·
    refine ⟨29309544878462644044524633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19539696585641762696349755 29309544878462644044524633)
    ·
      refine ⟨21982158658846983033393475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29309544878462644044524633 21982158658846983033393475)
      ·
        refine ⟨32973237988270474550090213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21982158658846983033393475 32973237988270474550090213)
        ·
          refine ⟨6182482122800713978141915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32973237988270474550090213 6182482122800713978141915)
          ·
            refine ⟨9273723184201070967212873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182482122800713978141915 9273723184201070967212873)
            ·
              refine ⟨6955292388150803225409655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9273723184201070967212873 6955292388150803225409655)
              ·
                refine ⟨10432938582226204838114483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6955292388150803225409655 10432938582226204838114483)
                ·
                  refine ⟨15649407873339307257171725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10432938582226204838114483 15649407873339307257171725)
                  ·
                    refine ⟨5868527952502240221439397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15649407873339307257171725 5868527952502240221439397)
                    ·
                      refine ⟨1100348991094170041519887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5868527952502240221439397 1100348991094170041519887)
                      ·
                        rfl

theorem cell23_2142922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2142922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142922 prefixEnd_2142922 := by exact prefixLift 2142922
  have htrace : WordTrace (prefixWord ++ tailWord_2142922) baseStart_2142922 baseEnd_2142922 := by
    simpa [prefixWord, tailWord_2142922, baseEnd_2142922] using wordTrace_append hprefix tailTrace_2142922
  have hstable : (prefixWord ++ tailWord_2142922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142922).length < 2 ^ (prefixWord ++ tailWord_2142922).sum := by decide
  have hdescent : baseEnd_2142922 < baseStart_2142922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2142949 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_2142949 : Nat := 118140960795 + 2142949 * 2 ^ 59
def prefixEnd_2142949 : Nat := 4983230072969 + 3 ^ 40 * 2142949 * 2
def baseEnd_2142949 : Nat := 366787618357280478627421

theorem tailTrace_2142949 : CollatzResearch.WordTrace tailWord_2142949 prefixEnd_2142949 366787618357280478627421 := by
  unfold tailWord_2142949
  simp only [CollatzResearch.WordTrace]
  refine ⟨78159771113469234396631901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52106514075646156264421267 78159771113469234396631901)
  ·
    refine ⟨29309914167550962898736963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78159771113469234396631901 29309914167550962898736963)
    ·
      refine ⟨43964871251326444348105445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29309914167550962898736963 43964871251326444348105445)
      ·
        refine ⟨8243413359623708315269771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43964871251326444348105445 8243413359623708315269771)
        ·
          refine ⟨12365120039435562472904657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8243413359623708315269771 12365120039435562472904657)
          ·
            refine ⟨9273840029576671854678493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12365120039435562472904657 9273840029576671854678493)
            ·
              refine ⟨3477690011091251945504435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9273840029576671854678493 3477690011091251945504435)
              ·
                refine ⟨5216535016636877918256653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477690011091251945504435 5216535016636877918256653)
                ·
                  refine ⟨1956200631238829219346245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5216535016636877918256653 1956200631238829219346245)
                  ·
                    refine ⟨366787618357280478627421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956200631238829219346245 366787618357280478627421)
                    ·
                      rfl

theorem cell23_2142949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_2142949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2142949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2142949 prefixEnd_2142949 := by exact prefixLift 2142949
  have htrace : WordTrace (prefixWord ++ tailWord_2142949) baseStart_2142949 baseEnd_2142949 := by
    simpa [prefixWord, tailWord_2142949, baseEnd_2142949] using wordTrace_append hprefix tailTrace_2142949
  have hstable : (prefixWord ++ tailWord_2142949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2142949).length < 2 ^ (prefixWord ++ tailWord_2142949).sum := by decide
  have hdescent : baseEnd_2142949 < baseStart_2142949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2142949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143029 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2143029 : Nat := 118140960795 + 2143029 * 2 ^ 59
def prefixEnd_2143029 : Nat := 4983230072969 + 3 ^ 40 * 2143029 * 2
def baseEnd_2143029 : Nat := 1100403933524201122881895

theorem tailTrace_2143029 : CollatzResearch.WordTrace tailWord_2143029 prefixEnd_2143029 1100403933524201122881895 := by
  unfold tailWord_2143029
  simp only [CollatzResearch.WordTrace]
  refine ⟨78162688953179408059544141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52108459302119605373029427 78162688953179408059544141)
  ·
    refine ⟨29311008357442278022329053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78162688953179408059544141 29311008357442278022329053)
    ·
      refine ⟨10991628134040854258373395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29311008357442278022329053 10991628134040854258373395)
      ·
        refine ⟨16487442201061281387560093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10991628134040854258373395 16487442201061281387560093)
        ·
          refine ⟨6182790825397980520335035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16487442201061281387560093 6182790825397980520335035)
          ·
            refine ⟨9274186238096970780502553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182790825397980520335035 9274186238096970780502553)
            ·
              refine ⟨6955639678572728085376915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9274186238096970780502553 6955639678572728085376915)
              ·
                refine ⟨10433459517859092128065373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6955639678572728085376915 10433459517859092128065373)
                ·
                  refine ⟨3912547319197159548024515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10433459517859092128065373 3912547319197159548024515)
                  ·
                    refine ⟨5868820978795739322036773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3912547319197159548024515 5868820978795739322036773)
                    ·
                      refine ⟨1100403933524201122881895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5868820978795739322036773 1100403933524201122881895)
                      ·
                        rfl

theorem cell23_2143029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2143029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143029 prefixEnd_2143029 := by exact prefixLift 2143029
  have htrace : WordTrace (prefixWord ++ tailWord_2143029) baseStart_2143029 baseEnd_2143029 := by
    simpa [prefixWord, tailWord_2143029, baseEnd_2143029] using wordTrace_append hprefix tailTrace_2143029
  have hstable : (prefixWord ++ tailWord_2143029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143029).length < 2 ^ (prefixWord ++ tailWord_2143029).sum := by decide
  have hdescent : baseEnd_2143029 < baseStart_2143029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143052 : List Nat := [2, 2, 1, 3, 3, 2, 10]
def baseStart_2143052 : Nat := 118140960795 + 2143052 * 2 ^ 59
def prefixEnd_2143052 : Nat := 4983230072969 + 3 ^ 40 * 2143052 * 2
def baseEnd_2143052 : Nat := 13585379550361167072769

theorem tailTrace_2143052 : CollatzResearch.WordTrace tailWord_2143052 prefixEnd_2143052 13585379550361167072769 := by
  unfold tailWord_2143052
  simp only [CollatzResearch.WordTrace]
  refine ⟨39081763916048041493815705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52109018554730721991754273 39081763916048041493815705)
  ·
    refine ⟨29311322937036031120361779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39081763916048041493815705 29311322937036031120361779)
    ·
      refine ⟨43966984405554046680542669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29311322937036031120361779 43966984405554046680542669)
      ·
        refine ⟨16487619152082767505203501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43966984405554046680542669 16487619152082767505203501)
        ·
          refine ⟨6182857182031037814451313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16487619152082767505203501 6182857182031037814451313)
          ·
            refine ⟨4637142886523278360838485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6182857182031037814451313 4637142886523278360838485)
            ·
              refine ⟨13585379550361167072769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4637142886523278360838485 13585379550361167072769)
              ·
                rfl

theorem cell23_2143052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 10].length) (baseStart_2143052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143052 prefixEnd_2143052 := by exact prefixLift 2143052
  have htrace : WordTrace (prefixWord ++ tailWord_2143052) baseStart_2143052 baseEnd_2143052 := by
    simpa [prefixWord, tailWord_2143052, baseEnd_2143052] using wordTrace_append hprefix tailTrace_2143052
  have hstable : (prefixWord ++ tailWord_2143052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143052).length < 2 ^ (prefixWord ++ tailWord_2143052).sum := by decide
  have hdescent : baseEnd_2143052 < baseStart_2143052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143063 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 3, 2, 2]
def baseStart_2143063 : Nat := 118140960795 + 2143063 * 2 ^ 59
def prefixEnd_2143063 : Nat := 4983230072969 + 3 ^ 40 * 2143063 * 2
def baseEnd_2143063 : Nat := 1100421391866453989856739

theorem tailTrace_2143063 : CollatzResearch.WordTrace tailWord_2143063 prefixEnd_2143063 1100421391866453989856739 := by
  unfold tailWord_2143063
  simp only [CollatzResearch.WordTrace]
  refine ⟨78163929035056231866281843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52109286023370821244187895 78163929035056231866281843)
  ·
    refine ⟨117245893552584347799422765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78163929035056231866281843 117245893552584347799422765)
    ·
      refine ⟨43967210082219130424783537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117245893552584347799422765 43967210082219130424783537)
      ·
        refine ⟨32975407561664347818587653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43967210082219130424783537 32975407561664347818587653)
        ·
          refine ⟨6182888917812065215985185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32975407561664347818587653 6182888917812065215985185)
          ·
            refine ⟨4637166688359048911988889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6182888917812065215985185 4637166688359048911988889)
            ·
              refine ⟨3477875016269286683991667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637166688359048911988889 3477875016269286683991667)
              ·
                refine ⟨5216812524403930025987501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477875016269286683991667 5216812524403930025987501)
                ·
                  refine ⟨1956304696651473759745313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5216812524403930025987501 1956304696651473759745313)
                  ·
                    refine ⟨1467228522488605319808985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1956304696651473759745313 1467228522488605319808985)
                    ·
                      refine ⟨1100421391866453989856739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467228522488605319808985 1100421391866453989856739)
                      ·
                        rfl

theorem cell23_2143063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_2143063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143063 prefixEnd_2143063 := by exact prefixLift 2143063
  have htrace : WordTrace (prefixWord ++ tailWord_2143063) baseStart_2143063 baseEnd_2143063 := by
    simpa [prefixWord, tailWord_2143063, baseEnd_2143063] using wordTrace_append hprefix tailTrace_2143063
  have hstable : (prefixWord ++ tailWord_2143063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143063).length < 2 ^ (prefixWord ++ tailWord_2143063).sum := by decide
  have hdescent : baseEnd_2143063 < baseStart_2143063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143076 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_2143076 : Nat := 118140960795 + 2143076 * 2 ^ 59
def prefixEnd_2143076 : Nat := 4983230072969 + 3 ^ 40 * 2143076 * 2
def baseEnd_2143076 : Nat := 1100428067114962438994179

theorem tailTrace_2143076 : CollatzResearch.WordTrace tailWord_2143076 prefixEnd_2143076 1100428067114962438994179 := by
  unfold tailWord_2143076
  simp only [CollatzResearch.WordTrace]
  refine ⟨39082201592004567543252541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52109602122672756724336721 39082201592004567543252541)
  ·
    refine ⟨14655825597001712828719703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39082201592004567543252541 14655825597001712828719703)
    ·
      refine ⟨21983738395502569243079555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14655825597001712828719703 21983738395502569243079555)
      ·
        refine ⟨32975607593253853864619333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21983738395502569243079555 32975607593253853864619333)
        ·
          refine ⟨6182926423735097599616125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32975607593253853864619333 6182926423735097599616125)
          ·
            refine ⟨2318597408900661599856047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6182926423735097599616125 2318597408900661599856047)
            ·
              refine ⟨3477896113350992399784071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318597408900661599856047 3477896113350992399784071)
              ·
                refine ⟨5216844170026488599676107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3477896113350992399784071 5216844170026488599676107)
                ·
                  refine ⟨7825266255039732899514161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5216844170026488599676107 7825266255039732899514161)
                  ·
                    refine ⟨5868949691279799674635621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7825266255039732899514161 5868949691279799674635621)
                    ·
                      refine ⟨1100428067114962438994179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5868949691279799674635621 1100428067114962438994179)
                      ·
                        rfl

theorem cell23_2143076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_2143076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143076 prefixEnd_2143076 := by exact prefixLift 2143076
  have htrace : WordTrace (prefixWord ++ tailWord_2143076) baseStart_2143076 baseEnd_2143076 := by
    simpa [prefixWord, tailWord_2143076, baseEnd_2143076] using wordTrace_append hprefix tailTrace_2143076
  have hstable : (prefixWord ++ tailWord_2143076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143076).length < 2 ^ (prefixWord ++ tailWord_2143076).sum := by decide
  have hdescent : baseEnd_2143076 < baseStart_2143076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143153 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 1, 4, 2]
def baseStart_2143153 : Nat := 118140960795 + 2143153 * 2 ^ 59
def prefixEnd_2143153 : Nat := 4983230072969 + 3 ^ 40 * 2143153 * 2
def baseEnd_2143153 : Nat := 1100467605125358637731325

theorem tailTrace_2143153 : CollatzResearch.WordTrace tailWord_2143153 prefixEnd_2143153 1100467605125358637731325 := by
  unfold tailWord_2143153
  simp only [CollatzResearch.WordTrace]
  refine ⟨78167211604730177237058113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52111474403153451491372075 78167211604730177237058113)
  ·
    refine ⟨58625408703547632927793585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78167211604730177237058113 58625408703547632927793585)
    ·
      refine ⟨43969056527660724695845189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58625408703547632927793585 43969056527660724695845189)
      ·
        refine ⟨8244198098936385880470973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43969056527660724695845189 8244198098936385880470973)
        ·
          refine ⟨3091574287101144705176615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8244198098936385880470973 3091574287101144705176615)
          ·
            refine ⟨4637361430651717057764923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091574287101144705176615 4637361430651717057764923)
            ·
              refine ⟨6956042145977575586647385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4637361430651717057764923 6956042145977575586647385)
              ·
                refine ⟨5217031609483181689985539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6956042145977575586647385 5217031609483181689985539)
                ·
                  refine ⟨7825547414224772534978309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217031609483181689985539 7825547414224772534978309)
                  ·
                    refine ⟨1467290140167144850308433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7825547414224772534978309 1467290140167144850308433)
                    ·
                      refine ⟨1100467605125358637731325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467290140167144850308433 1100467605125358637731325)
                      ·
                        rfl

theorem cell23_2143153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_2143153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143153 prefixEnd_2143153 := by exact prefixLift 2143153
  have htrace : WordTrace (prefixWord ++ tailWord_2143153) baseStart_2143153 baseEnd_2143153 := by
    simpa [prefixWord, tailWord_2143153, baseEnd_2143153] using wordTrace_append hprefix tailTrace_2143153
  have hstable : (prefixWord ++ tailWord_2143153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143153).length < 2 ^ (prefixWord ++ tailWord_2143153).sum := by decide
  have hdescent : baseEnd_2143153 < baseStart_2143153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143186 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2143186 : Nat := 118140960795 + 2143186 * 2 ^ 59
def prefixEnd_2143186 : Nat := 4983230072969 + 3 ^ 40 * 2143186 * 2
def baseEnd_2143186 : Nat := 1100484549986957008618673

theorem tailTrace_2143186 : CollatzResearch.WordTrace tailWord_2143186 prefixEnd_2143186 1100484549986957008618673 := by
  unfold tailWord_2143186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19542103803402655968252353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52112276809073749248672941 19542103803402655968252353)
  ·
    refine ⟨14656577852551991976189265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19542103803402655968252353 14656577852551991976189265)
    ·
      refine ⟨10992433389413993982141949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14656577852551991976189265 10992433389413993982141949)
      ·
        refine ⟨4122162521030247743303231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10992433389413993982141949 4122162521030247743303231)
        ·
          refine ⟨6183243781545371614954847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122162521030247743303231 6183243781545371614954847)
          ·
            refine ⟨9274865672318057422432271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183243781545371614954847 9274865672318057422432271)
            ·
              refine ⟨13912298508477086133648407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9274865672318057422432271 13912298508477086133648407)
              ·
                refine ⟨20868447762715629200472611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13912298508477086133648407 20868447762715629200472611)
                ·
                  refine ⟨31302671644073443800708917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20868447762715629200472611 31302671644073443800708917)
                  ·
                    refine ⟨2934625466631885356316461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31302671644073443800708917 2934625466631885356316461)
                    ·
                      refine ⟨1100484549986957008618673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2934625466631885356316461 1100484549986957008618673)
                      ·
                        rfl

theorem cell23_2143186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2143186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143186 prefixEnd_2143186 := by exact prefixLift 2143186
  have htrace : WordTrace (prefixWord ++ tailWord_2143186) baseStart_2143186 baseEnd_2143186 := by
    simpa [prefixWord, tailWord_2143186, baseEnd_2143186] using wordTrace_append hprefix tailTrace_2143186
  have hstable : (prefixWord ++ tailWord_2143186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143186).length < 2 ^ (prefixWord ++ tailWord_2143186).sum := by decide
  have hdescent : baseEnd_2143186 < baseStart_2143186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143221 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2143221 : Nat := 118140960795 + 2143221 * 2 ^ 59
def prefixEnd_2143221 : Nat := 4983230072969 + 3 ^ 40 * 2143221 * 2
def baseEnd_2143221 : Nat := 1100502521809864371681013

theorem tailTrace_2143221 : CollatzResearch.WordTrace tailWord_2143221 prefixEnd_2143221 1100502521809864371681013 := by
  unfold tailWord_2143221
  simp only [CollatzResearch.WordTrace]
  refine ⟨78169691768483824850533517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52113127845655883233689011 78169691768483824850533517)
  ·
    refine ⟨29313634413181434318950069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78169691768483824850533517 29313634413181434318950069)
    ·
      refine ⟨2748153226235759467401569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29313634413181434318950069 2748153226235759467401569)
      ·
        refine ⟨2061114919676819600551177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2748153226235759467401569 2061114919676819600551177)
        ·
          refine ⟨1545836189757614700413383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2061114919676819600551177 1545836189757614700413383)
          ·
            refine ⟨2318754284636422050620075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545836189757614700413383 2318754284636422050620075)
            ·
              refine ⟨3478131426954633075930113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318754284636422050620075 3478131426954633075930113)
              ·
                refine ⟨2608598570215974806947585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3478131426954633075930113 2608598570215974806947585)
                ·
                  refine ⟨1956448927661981105210689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2608598570215974806947585 1956448927661981105210689)
                  ·
                    refine ⟨1467336695746485828908017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1956448927661981105210689 1467336695746485828908017)
                    ·
                      refine ⟨1100502521809864371681013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467336695746485828908017 1100502521809864371681013)
                      ·
                        rfl

theorem cell23_2143221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2143221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143221 prefixEnd_2143221 := by exact prefixLift 2143221
  have htrace : WordTrace (prefixWord ++ tailWord_2143221) baseStart_2143221 baseEnd_2143221 := by
    simpa [prefixWord, tailWord_2143221, baseEnd_2143221] using wordTrace_append hprefix tailTrace_2143221
  have hstable : (prefixWord ++ tailWord_2143221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143221).length < 2 ^ (prefixWord ++ tailWord_2143221).sum := by decide
  have hdescent : baseEnd_2143221 < baseStart_2143221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143239 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2143239 : Nat := 118140960795 + 2143239 * 2 ^ 59
def prefixEnd_2143239 : Nat := 4983230072969 + 3 ^ 40 * 2143239 * 2
def baseEnd_2143239 : Nat := 1100511764461645301255929

theorem tailTrace_2143239 : CollatzResearch.WordTrace tailWord_2143239 prefixEnd_2143239 1100511764461645301255929 := by
  unfold tailWord_2143239
  simp only [CollatzResearch.WordTrace]
  refine ⟨78170348282418613924688771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52113565521612409283125847 78170348282418613924688771)
  ·
    refine ⟨117255522423627920887033157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78170348282418613924688771 117255522423627920887033157)
    ·
      refine ⟨21985410454430235166318717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117255522423627920887033157 21985410454430235166318717)
      ·
        refine ⟨8244528920411338187369519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21985410454430235166318717 8244528920411338187369519)
        ·
          refine ⟨12366793380617007281054279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8244528920411338187369519 12366793380617007281054279)
          ·
            refine ⟨18550190070925510921581419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12366793380617007281054279 18550190070925510921581419)
            ·
              refine ⟨27825285106388266382372129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18550190070925510921581419 27825285106388266382372129)
              ·
                refine ⟨20868963829791199786779097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27825285106388266382372129 20868963829791199786779097)
                ·
                  refine ⟨15651722872343399840084323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20868963829791199786779097 15651722872343399840084323)
                  ·
                    refine ⟨23477584308515099760126485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15651722872343399840084323 23477584308515099760126485)
                    ·
                      refine ⟨1100511764461645301255929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23477584308515099760126485 1100511764461645301255929)
                      ·
                        rfl

theorem cell23_2143239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2143239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143239 prefixEnd_2143239 := by exact prefixLift 2143239
  have htrace : WordTrace (prefixWord ++ tailWord_2143239) baseStart_2143239 baseEnd_2143239 := by
    simpa [prefixWord, tailWord_2143239, baseEnd_2143239] using wordTrace_append hprefix tailTrace_2143239
  have hstable : (prefixWord ++ tailWord_2143239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143239).length < 2 ^ (prefixWord ++ tailWord_2143239).sum := by decide
  have hdescent : baseEnd_2143239 < baseStart_2143239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143246 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2143246 : Nat := 118140960795 + 2143246 * 2 ^ 59
def prefixEnd_2143246 : Nat := 4983230072969 + 3 ^ 40 * 2143246 * 2
def baseEnd_2143246 : Nat := 1100515358826226773868397

theorem tailTrace_2143246 : CollatzResearch.WordTrace tailWord_2143246 prefixEnd_2143246 1100515358826226773868397 := by
  unfold tailWord_2143246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9771325449174156765024199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52113735728928836080129061 9771325449174156765024199)
  ·
    refine ⟨14656988173761235147536299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9771325449174156765024199 14656988173761235147536299)
    ·
      refine ⟨21985482260641852721304449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14656988173761235147536299 21985482260641852721304449)
      ·
        refine ⟨16489111695481389540978337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21985482260641852721304449 16489111695481389540978337)
        ·
          refine ⟨12366833771611042155733753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16489111695481389540978337 12366833771611042155733753)
          ·
            refine ⟨9275125328708281616800315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12366833771611042155733753 9275125328708281616800315)
            ·
              refine ⟨13912687993062422425200473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9275125328708281616800315 13912687993062422425200473)
              ·
                refine ⟨10434515994796816818900355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13912687993062422425200473 10434515994796816818900355)
                ·
                  refine ⟨15651773992195225228350533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10434515994796816818900355 15651773992195225228350533)
                  ·
                    refine ⟨2934707623536604730315725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15651773992195225228350533 2934707623536604730315725)
                    ·
                      refine ⟨1100515358826226773868397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2934707623536604730315725 1100515358826226773868397)
                      ·
                        rfl

theorem cell23_2143246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2143246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143246 prefixEnd_2143246 := by exact prefixLift 2143246
  have htrace : WordTrace (prefixWord ++ tailWord_2143246) baseStart_2143246 baseEnd_2143246 := by
    simpa [prefixWord, tailWord_2143246, baseEnd_2143246] using wordTrace_append hprefix tailTrace_2143246
  have hstable : (prefixWord ++ tailWord_2143246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143246).length < 2 ^ (prefixWord ++ tailWord_2143246).sum := by decide
  have hdescent : baseEnd_2143246 < baseStart_2143246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143249 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 6]
def baseStart_2143249 : Nat := 118140960795 + 2143249 * 2 ^ 59
def prefixEnd_2143249 : Nat := 4983230072969 + 3 ^ 40 * 2143249 * 2
def baseEnd_2143249 : Nat := 122279655474243362458987

theorem tailTrace_2143249 : CollatzResearch.WordTrace tailWord_2143249 prefixEnd_2143249 122279655474243362458987 := by
  unfold tailWord_2143249
  simp only [CollatzResearch.WordTrace]
  refine ⟨78170713012382385632552801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52113808674921590421701867 78170713012382385632552801)
  ·
    refine ⟨58628034759286789224414601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78170713012382385632552801 58628034759286789224414601)
    ·
      refine ⟨43971026069465091918310951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58628034759286789224414601 43971026069465091918310951)
      ·
        refine ⟨65956539104197637877466427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43971026069465091918310951 65956539104197637877466427)
        ·
          refine ⟨98934808656296456816199641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65956539104197637877466427 98934808656296456816199641)
          ·
            refine ⟨74201106492222342612149731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98934808656296456816199641 74201106492222342612149731)
            ·
              refine ⟨111301659738333513918224597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74201106492222342612149731 111301659738333513918224597)
              ·
                refine ⟨2608632650117191732458389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111301659738333513918224597 2608632650117191732458389)
                ·
                  refine ⟨122279655474243362458987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2608632650117191732458389 122279655474243362458987)
                  ·
                    rfl

theorem cell23_2143249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 6].length) (baseStart_2143249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143249 prefixEnd_2143249 := by exact prefixLift 2143249
  have htrace : WordTrace (prefixWord ++ tailWord_2143249) baseStart_2143249 baseEnd_2143249 := by
    simpa [prefixWord, tailWord_2143249, baseEnd_2143249] using wordTrace_append hprefix tailTrace_2143249
  have hstable : (prefixWord ++ tailWord_2143249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143249).length < 2 ^ (prefixWord ++ tailWord_2143249).sum := by decide
  have hdescent : baseEnd_2143249 < baseStart_2143249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143343 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 2, 4]
def baseStart_2143343 : Nat := 118140960795 + 2143343 * 2 ^ 59
def prefixEnd_2143343 : Nat := 4983230072969 + 3 ^ 40 * 2143343 * 2
def baseEnd_2143343 : Nat := 366855055483237631451817

theorem tailTrace_2143343 : CollatzResearch.WordTrace tailWord_2143343 prefixEnd_2143343 366855055483237631451817 := by
  unfold tailWord_2143343
  simp only [CollatzResearch.WordTrace]
  refine ⟨78174141474041839686474683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52116094316027893124316455 78174141474041839686474683)
  ·
    refine ⟨117261212211062759529712025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78174141474041839686474683 117261212211062759529712025)
    ·
      refine ⟨87945909158297069647284019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117261212211062759529712025 87945909158297069647284019)
      ·
        refine ⟨131918863737445604470926029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87945909158297069647284019 131918863737445604470926029)
        ·
          refine ⟨49469573901542101676597261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131918863737445604470926029 49469573901542101676597261)
          ·
            refine ⟨18551090213078288128723973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49469573901542101676597261 18551090213078288128723973)
            ·
              refine ⟨3478329414952179024135745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18551090213078288128723973 3478329414952179024135745)
              ·
                refine ⟨2608747061214134268101809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3478329414952179024135745 2608747061214134268101809)
                ·
                  refine ⟨1956560295910600701076357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2608747061214134268101809 1956560295910600701076357)
                  ·
                    refine ⟨366855055483237631451817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956560295910600701076357 366855055483237631451817)
                    ·
                      rfl

theorem cell23_2143343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_2143343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143343 prefixEnd_2143343 := by exact prefixLift 2143343
  have htrace : WordTrace (prefixWord ++ tailWord_2143343) baseStart_2143343 baseEnd_2143343 := by
    simpa [prefixWord, tailWord_2143343, baseEnd_2143343] using wordTrace_append hprefix tailTrace_2143343
  have hstable : (prefixWord ++ tailWord_2143343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143343).length < 2 ^ (prefixWord ++ tailWord_2143343).sum := by decide
  have hdescent : baseEnd_2143343 < baseStart_2143343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143346 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2143346 : Nat := 118140960795 + 2143346 * 2 ^ 59
def prefixEnd_2143346 : Nat := 4983230072969 + 3 ^ 40 * 2143346 * 2
def baseEnd_2143346 : Nat := 1100566706891676382617937

theorem tailTrace_2143346 : CollatzResearch.WordTrace tailWord_2143346 prefixEnd_2143346 1100566706891676382617937 := by
  unfold tailWord_2143346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19543562723257742799708473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52116167262020647465889261 19543562723257742799708473)
  ·
    refine ⟨14657672042443307099781355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19543562723257742799708473 14657672042443307099781355)
    ·
      refine ⟨21986508063664960649672033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14657672042443307099781355 21986508063664960649672033)
      ·
        refine ⟨16489881047748720487254025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21986508063664960649672033 16489881047748720487254025)
        ·
          refine ⟨12367410785811540365440519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16489881047748720487254025 12367410785811540365440519)
          ·
            refine ⟨18551116178717310548160779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12367410785811540365440519 18551116178717310548160779)
            ·
              refine ⟨27826674268075965822241169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18551116178717310548160779 27826674268075965822241169)
              ·
                refine ⟨20870005701056974366680877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27826674268075965822241169 20870005701056974366680877)
                ·
                  refine ⟨7826252137896365387505329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20870005701056974366680877 7826252137896365387505329)
                  ·
                    refine ⟨5869689103422274040628997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7826252137896365387505329 5869689103422274040628997)
                    ·
                      refine ⟨1100566706891676382617937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5869689103422274040628997 1100566706891676382617937)
                      ·
                        rfl

theorem cell23_2143346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2143346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143346 prefixEnd_2143346 := by exact prefixLift 2143346
  have htrace : WordTrace (prefixWord ++ tailWord_2143346) baseStart_2143346 baseEnd_2143346 := by
    simpa [prefixWord, tailWord_2143346, baseEnd_2143346] using wordTrace_append hprefix tailTrace_2143346
  have hstable : (prefixWord ++ tailWord_2143346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143346).length < 2 ^ (prefixWord ++ tailWord_2143346).sum := by decide
  have hdescent : baseEnd_2143346 < baseStart_2143346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143383 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_2143383 : Nat := 118140960795 + 2143383 * 2 ^ 59
def prefixEnd_2143383 : Nat := 4983230072969 + 3 ^ 40 * 2143383 * 2
def baseEnd_2143383 : Nat := 1100585705675892737855267

theorem tailTrace_2143383 : CollatzResearch.WordTrace tailWord_2143383 prefixEnd_2143383 1100585705675892737855267 := by
  unfold tailWord_2143383
  simp only [CollatzResearch.WordTrace]
  refine ⟨78175600393896926517930803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52117066929264617678620535 78175600393896926517930803)
  ·
    refine ⟨117263400590845389776896205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78175600393896926517930803 117263400590845389776896205)
    ·
      refine ⟨43973775221567021166336077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117263400590845389776896205 43973775221567021166336077)
      ·
        refine ⟨16490165708087632937376029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43973775221567021166336077 16490165708087632937376029)
        ·
          refine ⟨6183812140532862351516011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16490165708087632937376029 6183812140532862351516011)
          ·
            refine ⟨9275718210799293527274017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183812140532862351516011 9275718210799293527274017)
            ·
              refine ⟨6956788658099470145455513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9275718210799293527274017 6956788658099470145455513)
              ·
                refine ⟨5217591493574602609091635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6956788658099470145455513 5217591493574602609091635)
                ·
                  refine ⟨7826387240361903913637453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217591493574602609091635 7826387240361903913637453)
                  ·
                    refine ⟨2934895215135713967614045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7826387240361903913637453 2934895215135713967614045)
                    ·
                      refine ⟨1100585705675892737855267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2934895215135713967614045 1100585705675892737855267)
                      ·
                        rfl

theorem cell23_2143383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_2143383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143383 prefixEnd_2143383 := by exact prefixLift 2143383
  have htrace : WordTrace (prefixWord ++ tailWord_2143383) baseStart_2143383 baseEnd_2143383 := by
    simpa [prefixWord, tailWord_2143383, baseEnd_2143383] using wordTrace_append hprefix tailTrace_2143383
  have hstable : (prefixWord ++ tailWord_2143383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143383).length < 2 ^ (prefixWord ++ tailWord_2143383).sum := by decide
  have hdescent : baseEnd_2143383 < baseStart_2143383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143384 : List Nat := [2, 1, 2, 4, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2143384 : Nat := 118140960795 + 2143384 * 2 ^ 59
def prefixEnd_2143384 : Nat := 4983230072969 + 3 ^ 40 * 2143384 * 2
def baseEnd_2143384 : Nat := 1100586219156547233942763

theorem tailTrace_2143384 : CollatzResearch.WordTrace tailWord_2143384 prefixEnd_2143384 1100586219156547233942763 := by
  unfold tailWord_2143384
  simp only [CollatzResearch.WordTrace]
  refine ⟨39087818433446651844358603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52117091244595535792478137 39087818433446651844358603)
  ·
    refine ⟨58631727650169977766537905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39087818433446651844358603 58631727650169977766537905)
    ·
      refine ⟨43973795737627483324903429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58631727650169977766537905 43973795737627483324903429)
      ·
        refine ⟨8245086700805153123419393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43973795737627483324903429 8245086700805153123419393)
        ·
          refine ⟨6183815025603864842564545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8245086700805153123419393 6183815025603864842564545)
          ·
            refine ⟨4637861269202898631923409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6183815025603864842564545 4637861269202898631923409)
            ·
              refine ⟨3478395951902173973942557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637861269202898631923409 3478395951902173973942557)
              ·
                refine ⟨1304398481963315240228459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3478395951902173973942557 1304398481963315240228459)
                ·
                  refine ⟨1956597722944972860342689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304398481963315240228459 1956597722944972860342689)
                  ·
                    refine ⟨1467448292208729645257017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1956597722944972860342689 1467448292208729645257017)
                    ·
                      refine ⟨1100586219156547233942763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467448292208729645257017 1100586219156547233942763)
                      ·
                        rfl

theorem cell23_2143384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2143384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143384 prefixEnd_2143384 := by exact prefixLift 2143384
  have htrace : WordTrace (prefixWord ++ tailWord_2143384) baseStart_2143384 baseEnd_2143384 := by
    simpa [prefixWord, tailWord_2143384, baseEnd_2143384] using wordTrace_append hprefix tailTrace_2143384
  have hstable : (prefixWord ++ tailWord_2143384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143384).length < 2 ^ (prefixWord ++ tailWord_2143384).sum := by decide
  have hdescent : baseEnd_2143384 < baseStart_2143384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143394 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2143394 : Nat := 118140960795 + 2143394 * 2 ^ 59
def prefixEnd_2143394 : Nat := 4983230072969 + 3 ^ 40 * 2143394 * 2
def baseEnd_2143394 : Nat := 366863784654364064939239

theorem tailTrace_2143394 : CollatzResearch.WordTrace tailWord_2143394 prefixEnd_2143394 366863784654364064939239 := by
  unfold tailWord_2143394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19544000399214268849145309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52117334397904716931054157 19544000399214268849145309)
  ·
    refine ⟨7329000149705350818429491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19544000399214268849145309 7329000149705350818429491)
    ·
      refine ⟨10993500224558026227644237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329000149705350818429491 10993500224558026227644237)
      ·
        refine ⟨4122562584209259835366589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10993500224558026227644237 4122562584209259835366589)
        ·
          refine ⟨1545960969078472438262471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4122562584209259835366589 1545960969078472438262471)
          ·
            refine ⟨2318941453617708657393707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545960969078472438262471 2318941453617708657393707)
            ·
              refine ⟨3478412180426562986090561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318941453617708657393707 3478412180426562986090561)
              ·
                refine ⟨2608809135319922239567921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3478412180426562986090561 2608809135319922239567921)
                ·
                  refine ⟨1956606851489941679675941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2608809135319922239567921 1956606851489941679675941)
                  ·
                    refine ⟨366863784654364064939239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956606851489941679675941 366863784654364064939239)
                    ·
                      rfl

theorem cell23_2143394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2143394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143394 prefixEnd_2143394 := by exact prefixLift 2143394
  have htrace : WordTrace (prefixWord ++ tailWord_2143394) baseStart_2143394 baseEnd_2143394 := by
    simpa [prefixWord, tailWord_2143394, baseEnd_2143394] using wordTrace_append hprefix tailTrace_2143394
  have hstable : (prefixWord ++ tailWord_2143394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143394).length < 2 ^ (prefixWord ++ tailWord_2143394).sum := by decide
  have hdescent : baseEnd_2143394 < baseStart_2143394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143414 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2143414 : Nat := 118140960795 + 2143414 * 2 ^ 59
def prefixEnd_2143414 : Nat := 4983230072969 + 3 ^ 40 * 2143414 * 2
def baseEnd_2143414 : Nat := 1100601623576182116567625

theorem tailTrace_2143414 : CollatzResearch.WordTrace tailWord_2143414 prefixEnd_2143414 1100601623576182116567625 := by
  unfold tailWord_2143414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886045691049038675769331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52117820704523079208206197 4886045691049038675769331)
  ·
    refine ⟨7329068536573558013653997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4886045691049038675769331 7329068536573558013653997)
    ·
      refine ⟨2748400701215084255120249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7329068536573558013653997 2748400701215084255120249)
      ·
        refine ⟨2061300525911313191340187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2748400701215084255120249 2061300525911313191340187)
        ·
          refine ⟨3091950788866969787010281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061300525911313191340187 3091950788866969787010281)
          ·
            refine ⟨2318963091650227340257711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3091950788866969787010281 2318963091650227340257711)
            ·
              refine ⟨3478444637475341010386567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2318963091650227340257711 3478444637475341010386567)
              ·
                refine ⟨5217666956213011515579851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478444637475341010386567 5217666956213011515579851)
                ·
                  refine ⟨7826500434319517273369777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5217666956213011515579851 7826500434319517273369777)
                  ·
                    refine ⟨5869875325739637955027333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7826500434319517273369777 5869875325739637955027333)
                    ·
                      refine ⟨1100601623576182116567625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5869875325739637955027333 1100601623576182116567625)
                      ·
                        rfl

theorem cell23_2143414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2143414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143414 prefixEnd_2143414 := by exact prefixLift 2143414
  have htrace : WordTrace (prefixWord ++ tailWord_2143414) baseStart_2143414 baseEnd_2143414 := by
    simpa [prefixWord, tailWord_2143414, baseEnd_2143414] using wordTrace_append hprefix tailTrace_2143414
  have hstable : (prefixWord ++ tailWord_2143414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143414).length < 2 ^ (prefixWord ++ tailWord_2143414).sum := by decide
  have hdescent : baseEnd_2143414 < baseStart_2143414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143417 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 2, 1, 3]
def baseStart_2143417 : Nat := 118140960795 + 2143417 * 2 ^ 59
def prefixEnd_2143417 : Nat := 4983230072969 + 3 ^ 40 * 2143417 * 2
def baseEnd_2143417 : Nat := 1100603164018145604830111

theorem tailTrace_2143417 : CollatzResearch.WordTrace tailWord_2143417 prefixEnd_2143417 1100603164018145604830111 := by
  unfold tailWord_2143417
  simp only [CollatzResearch.WordTrace]
  refine ⟨78176840475773750324668505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52117893650515833549779003 78176840475773750324668505)
  ·
    refine ⟨58632630356830312743501379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78176840475773750324668505 58632630356830312743501379)
    ·
      refine ⟨87948945535245469115252069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58632630356830312743501379 87948945535245469115252069)
      ·
        refine ⟨16490427287858525459109763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87948945535245469115252069 16490427287858525459109763)
        ·
          refine ⟨24735640931787788188664645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16490427287858525459109763 24735640931787788188664645)
          ·
            refine ⟨4637932674710210285374621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24735640931787788188664645 4637932674710210285374621)
            ·
              refine ⟨1739224753016328857015483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4637932674710210285374621 1739224753016328857015483)
              ·
                refine ⟨2608837129524493285523225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739224753016328857015483 2608837129524493285523225)
                ·
                  refine ⟨1956627847143369964142419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2608837129524493285523225 1956627847143369964142419)
                  ·
                    refine ⟨2934941770715054946213629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1956627847143369964142419 2934941770715054946213629)
                    ·
                      refine ⟨1100603164018145604830111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2934941770715054946213629 1100603164018145604830111)
                      ·
                        rfl

theorem cell23_2143417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_2143417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143417 prefixEnd_2143417 := by exact prefixLift 2143417
  have htrace : WordTrace (prefixWord ++ tailWord_2143417) baseStart_2143417 baseEnd_2143417 := by
    simpa [prefixWord, tailWord_2143417, baseEnd_2143417] using wordTrace_append hprefix tailTrace_2143417
  have hstable : (prefixWord ++ tailWord_2143417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143417).length < 2 ^ (prefixWord ++ tailWord_2143417).sum := by decide
  have hdescent : baseEnd_2143417 < baseStart_2143417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143474 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_2143474 : Nat := 118140960795 + 2143474 * 2 ^ 59
def prefixEnd_2143474 : Nat := 4983230072969 + 3 ^ 40 * 2143474 * 2
def baseEnd_2143474 : Nat := 1100632432415451881817349

theorem tailTrace_2143474 : CollatzResearch.WordTrace tailWord_2143474 prefixEnd_2143474 1100632432415451881817349 := by
  unfold tailWord_2143474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19544729859141812264873369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52119279624378166039662317 19544729859141812264873369)
  ·
    refine ⟨14658547394356359198655027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19544729859141812264873369 14658547394356359198655027)
    ·
      refine ⟨21987821091534538797982541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14658547394356359198655027 21987821091534538797982541)
      ·
        refine ⟨8245432909325452049243453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21987821091534538797982541 8245432909325452049243453)
        ·
          refine ⟨3092037340997044518466295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8245432909325452049243453 3092037340997044518466295)
          ·
            refine ⟨4638056011495566777699443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092037340997044518466295 4638056011495566777699443)
            ·
              refine ⟨6957084017243350166549165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638056011495566777699443 6957084017243350166549165)
              ·
                refine ⟨2608906506466256312455937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6957084017243350166549165 2608906506466256312455937)
                ·
                  refine ⟨1956679879849692234341953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2608906506466256312455937 1956679879849692234341953)
                  ·
                    refine ⟨1467509909887269175756465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1956679879849692234341953 1467509909887269175756465)
                    ·
                      refine ⟨1100632432415451881817349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467509909887269175756465 1100632432415451881817349)
                      ·
                        rfl

theorem cell23_2143474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_2143474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143474 prefixEnd_2143474 := by exact prefixLift 2143474
  have htrace : WordTrace (prefixWord ++ tailWord_2143474) baseStart_2143474 baseEnd_2143474 := by
    simpa [prefixWord, tailWord_2143474, baseEnd_2143474] using wordTrace_append hprefix tailTrace_2143474
  have hstable : (prefixWord ++ tailWord_2143474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143474).length < 2 ^ (prefixWord ++ tailWord_2143474).sum := by decide
  have hdescent : baseEnd_2143474 < baseStart_2143474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143493 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_2143493 : Nat := 118140960795 + 2143493 * 2 ^ 59
def prefixEnd_2143493 : Nat := 4983230072969 + 3 ^ 40 * 2143493 * 2
def baseEnd_2143493 : Nat := 366880729515962435826587

theorem tailTrace_2143493 : CollatzResearch.WordTrace tailWord_2143493 prefixEnd_2143493 366880729515962435826587 := by
  unfold tailWord_2143493
  simp only [CollatzResearch.WordTrace]
  refine ⟨78179612423498415304435133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52119741615665610202956755 78179612423498415304435133)
  ·
    refine ⟨29317354658811905739163175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78179612423498415304435133 29317354658811905739163175)
    ·
      refine ⟨43976031988217858608744763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29317354658811905739163175 43976031988217858608744763)
      ·
        refine ⟨65964047982326787913117145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43976031988217858608744763 65964047982326787913117145)
        ·
          refine ⟨49473035986745090934837859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65964047982326787913117145 49473035986745090934837859)
          ·
            refine ⟨74209553980117636402256789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49473035986745090934837859 74209553980117636402256789)
            ·
              refine ⟨3478572842818014206355787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74209553980117636402256789 3478572842818014206355787)
              ·
                refine ⟨5217859264227021309533681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478572842818014206355787 5217859264227021309533681)
                ·
                  refine ⟨3913394448170265982150261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5217859264227021309533681 3913394448170265982150261)
                  ·
                    refine ⟨366880729515962435826587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3913394448170265982150261 366880729515962435826587)
                    ·
                      rfl

theorem cell23_2143493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_2143493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143493 prefixEnd_2143493 := by exact prefixLift 2143493
  have htrace : WordTrace (prefixWord ++ tailWord_2143493) baseStart_2143493 baseEnd_2143493 := by
    simpa [prefixWord, tailWord_2143493, baseEnd_2143493] using wordTrace_append hprefix tailTrace_2143493
  have hstable : (prefixWord ++ tailWord_2143493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143493).length < 2 ^ (prefixWord ++ tailWord_2143493).sum := by decide
  have hdescent : baseEnd_2143493 < baseStart_2143493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143513 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 5, 6, 2]
def baseStart_2143513 : Nat := 118140960795 + 2143513 * 2 ^ 59
def prefixEnd_2143513 : Nat := 4983230072969 + 3 ^ 40 * 2143513 * 2
def baseEnd_2143513 : Nat := 1100652458160977229229669

theorem tailTrace_2143513 : CollatzResearch.WordTrace tailWord_2143513 prefixEnd_2143513 1100652458160977229229669 := by
  unfold tailWord_2143513
  simp only [CollatzResearch.WordTrace]
  refine ⟨78180341883425958720163193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52120227922283972480108795 78180341883425958720163193)
  ·
    refine ⟨58635256412569469040122395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78180341883425958720163193 58635256412569469040122395)
    ·
      refine ⟨87952884618854203560183593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58635256412569469040122395 87952884618854203560183593)
      ·
        refine ⟨65964663464140652670137695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87952884618854203560183593 65964663464140652670137695)
        ·
          refine ⟨98946995196210979005206543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65964663464140652670137695 98946995196210979005206543)
          ·
            refine ⟨148420492794316468507809815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98946995196210979005206543 148420492794316468507809815)
            ·
              refine ⟨222630739191474702761714723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148420492794316468507809815 222630739191474702761714723)
              ·
                refine ⟨333946108787212054142572085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222630739191474702761714723 333946108787212054142572085)
                ·
                  refine ⟨31307447698801130075866133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 333946108787212054142572085 31307447698801130075866133)
                  ·
                    refine ⟨1467536610881302972306225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31307447698801130075866133 1467536610881302972306225)
                    ·
                      refine ⟨1100652458160977229229669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467536610881302972306225 1100652458160977229229669)
                      ·
                        rfl

theorem cell23_2143513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_2143513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143513 prefixEnd_2143513 := by exact prefixLift 2143513
  have htrace : WordTrace (prefixWord ++ tailWord_2143513) baseStart_2143513 baseEnd_2143513 := by
    simpa [prefixWord, tailWord_2143513, baseEnd_2143513] using wordTrace_append hprefix tailTrace_2143513
  have hstable : (prefixWord ++ tailWord_2143513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143513).length < 2 ^ (prefixWord ++ tailWord_2143513).sum := by decide
  have hdescent : baseEnd_2143513 < baseStart_2143513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143550 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2143550 : Nat := 118140960795 + 2143550 * 2 ^ 59
def prefixEnd_2143550 : Nat := 4983230072969 + 3 ^ 40 * 2143550 * 2
def baseEnd_2143550 : Nat := 1100671456945193584466999

theorem tailTrace_2143550 : CollatzResearch.WordTrace tailWord_2143550 prefixEnd_2143550 1100671456945193584466999 := by
  unfold tailWord_2143550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9772711423036489254907513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52121127589527942692840069 9772711423036489254907513)
  ·
    refine ⟨7329533567277366941180635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9772711423036489254907513 7329533567277366941180635)
    ·
      refine ⟨10994300350916050411770953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329533567277366941180635 10994300350916050411770953)
      ·
        refine ⟨8245725263187037808828215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10994300350916050411770953 8245725263187037808828215)
        ·
          refine ⟨12368587894780556713242323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8245725263187037808828215 12368587894780556713242323)
          ·
            refine ⟨18552881842170835069863485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12368587894780556713242323 18552881842170835069863485)
            ·
              refine ⟨6957330690814063151198807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18552881842170835069863485 6957330690814063151198807)
              ·
                refine ⟨10435996036221094726798211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6957330690814063151198807 10435996036221094726798211)
                ·
                  refine ⟨15653994054331642090197317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10435996036221094726798211 15653994054331642090197317)
                  ·
                    refine ⟨2935123885187182891911997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15653994054331642090197317 2935123885187182891911997)
                    ·
                      refine ⟨1100671456945193584466999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2935123885187182891911997 1100671456945193584466999)
                      ·
                        rfl

theorem cell23_2143550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2143550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143550 prefixEnd_2143550 := by exact prefixLift 2143550
  have htrace : WordTrace (prefixWord ++ tailWord_2143550) baseStart_2143550 baseEnd_2143550 := by
    simpa [prefixWord, tailWord_2143550, baseEnd_2143550] using wordTrace_append hprefix tailTrace_2143550
  have hstable : (prefixWord ++ tailWord_2143550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143550).length < 2 ^ (prefixWord ++ tailWord_2143550).sum := by decide
  have hdescent : baseEnd_2143550 < baseStart_2143550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143573 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2143573 : Nat := 118140960795 + 2143573 * 2 ^ 59
def prefixEnd_2143573 : Nat := 4983230072969 + 3 ^ 40 * 2143573 * 2
def baseEnd_2143573 : Nat := 1100683267000246994479393

theorem tailTrace_2143573 : CollatzResearch.WordTrace tailWord_2143573 prefixEnd_2143573 1100683267000246994479393 := by
  unfold tailWord_2143573
  simp only [CollatzResearch.WordTrace]
  refine ⟨78182530263208588967347373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52121686842139059311564915 78182530263208588967347373)
  ·
    refine ⟨29318448848703220862755265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78182530263208588967347373 29318448848703220862755265)
    ·
      refine ⟨21988836636527415647066449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29318448848703220862755265 21988836636527415647066449)
      ·
        refine ⟨16491627477395561735299837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21988836636527415647066449 16491627477395561735299837)
        ·
          refine ⟨6184360304023335650737439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16491627477395561735299837 6184360304023335650737439)
          ·
            refine ⟨9276540456035003476106159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6184360304023335650737439 9276540456035003476106159)
            ·
              refine ⟨13914810684052505214159239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9276540456035003476106159 13914810684052505214159239)
              ·
                refine ⟨20872216026078757821238859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13914810684052505214159239 20872216026078757821238859)
                ·
                  refine ⟨31308324039118136731858289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20872216026078757821238859 31308324039118136731858289)
                  ·
                    refine ⟨23481243029338602548893717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31308324039118136731858289 23481243029338602548893717)
                    ·
                      refine ⟨1100683267000246994479393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23481243029338602548893717 1100683267000246994479393)
                      ·
                        rfl

theorem cell23_2143573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2143573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143573 prefixEnd_2143573 := by exact prefixLift 2143573
  have htrace : WordTrace (prefixWord ++ tailWord_2143573) baseStart_2143573 baseEnd_2143573 := by
    simpa [prefixWord, tailWord_2143573, baseEnd_2143573] using wordTrace_append hprefix tailTrace_2143573
  have hstable : (prefixWord ++ tailWord_2143573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143573).length < 2 ^ (prefixWord ++ tailWord_2143573).sum := by decide
  have hdescent : baseEnd_2143573 < baseStart_2143573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143597 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2143597 : Nat := 118140960795 + 2143597 * 2 ^ 59
def prefixEnd_2143597 : Nat := 4983230072969 + 3 ^ 40 * 2143597 * 2
def baseEnd_2143597 : Nat := 1100695590535954900579283

theorem tailTrace_2143597 : CollatzResearch.WordTrace tailWord_2143597 prefixEnd_2143597 1100695590535954900579283 := by
  unfold tailWord_2143597
  simp only [CollatzResearch.WordTrace]
  refine ⟨78183405615121641066221045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52122270410081094044147363 78183405615121641066221045)
  ·
    refine ⟨7329694276417653849958223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78183405615121641066221045 7329694276417653849958223)
    ·
      refine ⟨10994541414626480774937335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329694276417653849958223 10994541414626480774937335)
      ·
        refine ⟨16491812121939721162406003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10994541414626480774937335 16491812121939721162406003)
        ·
          refine ⟨24737718182909581743609005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16491812121939721162406003 24737718182909581743609005)
          ·
            refine ⟨9276644318591093153853377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24737718182909581743609005 9276644318591093153853377)
            ·
              refine ⟨6957483238943319865390033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9276644318591093153853377 6957483238943319865390033)
              ·
                refine ⟨5218112429207489899042525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6957483238943319865390033 5218112429207489899042525)
                ·
                  refine ⟨1956792160952808712140947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5218112429207489899042525 1956792160952808712140947)
                  ·
                    refine ⟨2935188241429213068211421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1956792160952808712140947 2935188241429213068211421)
                    ·
                      refine ⟨1100695590535954900579283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2935188241429213068211421 1100695590535954900579283)
                      ·
                        rfl

theorem cell23_2143597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2143597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143597 prefixEnd_2143597 := by exact prefixLift 2143597
  have htrace : WordTrace (prefixWord ++ tailWord_2143597) baseStart_2143597 baseEnd_2143597 := by
    simpa [prefixWord, tailWord_2143597, baseEnd_2143597] using wordTrace_append hprefix tailTrace_2143597
  have hstable : (prefixWord ++ tailWord_2143597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143597).length < 2 ^ (prefixWord ++ tailWord_2143597).sum := by decide
  have hdescent : baseEnd_2143597 < baseStart_2143597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143600 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 1, 5]
def baseStart_2143600 : Nat := 118140960795 + 2143600 * 2 ^ 59
def prefixEnd_2143600 : Nat := 4983230072969 + 3 ^ 40 * 2143600 * 2
def baseEnd_2143600 : Nat := 366899043659306129613923

theorem tailTrace_2143600 : CollatzResearch.WordTrace tailWord_2143600 prefixEnd_2143600 366899043659306129613923 := by
  unfold tailWord_2143600
  simp only [CollatzResearch.WordTrace]
  refine ⟨39091757517055386289290127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52122343356073848385720169 39091757517055386289290127)
  ·
    refine ⟨58637636275583079433935191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39091757517055386289290127 58637636275583079433935191)
    ·
      refine ⟨87956454413374619150902787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58637636275583079433935191 87956454413374619150902787)
      ·
        refine ⟨131934681620061928726354181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87956454413374619150902787 131934681620061928726354181)
        ·
          refine ⟨24737752803761611636191409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131934681620061928726354181 24737752803761611636191409)
          ·
            refine ⟨18553314602821208727143557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24737752803761611636191409 18553314602821208727143557)
            ·
              refine ⟨3478746488028976636339417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18553314602821208727143557 3478746488028976636339417)
              ·
                refine ⟨2609059866021732477254563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3478746488028976636339417 2609059866021732477254563)
                ·
                  refine ⟨3913589799032598715881845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609059866021732477254563 3913589799032598715881845)
                  ·
                    refine ⟨366899043659306129613923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3913589799032598715881845 366899043659306129613923)
                    ·
                      rfl

theorem cell23_2143600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_2143600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143600 prefixEnd_2143600 := by exact prefixLift 2143600
  have htrace : WordTrace (prefixWord ++ tailWord_2143600) baseStart_2143600 baseEnd_2143600 := by
    simpa [prefixWord, tailWord_2143600, baseEnd_2143600] using wordTrace_append hprefix tailTrace_2143600
  have hstable : (prefixWord ++ tailWord_2143600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143600).length < 2 ^ (prefixWord ++ tailWord_2143600).sum := by decide
  have hdescent : baseEnd_2143600 < baseStart_2143600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143613 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2143613 : Nat := 118140960795 + 2143613 * 2 ^ 59
def prefixEnd_2143613 : Nat := 4983230072969 + 3 ^ 40 * 2143613 * 2
def baseEnd_2143613 : Nat := 366901268742142279326403

theorem tailTrace_2143613 : CollatzResearch.WordTrace tailWord_2143613 prefixEnd_2143613 366901268742142279326403 := by
  unfold tailWord_2143613
  simp only [CollatzResearch.WordTrace]
  refine ⟨78183989183063675798803493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52122659455375783865868995 78183989183063675798803493)
  ·
    refine ⟨14659497971824439212275655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78183989183063675798803493 14659497971824439212275655)
    ·
      refine ⟨21989246957736658818413483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14659497971824439212275655 21989246957736658818413483)
      ·
        refine ⟨32983870436604988227620225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21989246957736658818413483 32983870436604988227620225)
        ·
          refine ⟨24737902827453741170715169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32983870436604988227620225 24737902827453741170715169)
          ·
            refine ⟨18553427120590305878036377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24737902827453741170715169 18553427120590305878036377)
            ·
              refine ⟨13915070340442729408527283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18553427120590305878036377 13915070340442729408527283)
              ·
                refine ⟨20872605510664094112790925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13915070340442729408527283 20872605510664094112790925)
                ·
                  refine ⟨7827227066499035292296597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20872605510664094112790925 7827227066499035292296597)
                  ·
                    refine ⟨366901268742142279326403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7827227066499035292296597 366901268742142279326403)
                    ·
                      rfl

theorem cell23_2143613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2143613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143613 prefixEnd_2143613 := by exact prefixLift 2143613
  have htrace : WordTrace (prefixWord ++ tailWord_2143613) baseStart_2143613 baseEnd_2143613 := by
    simpa [prefixWord, tailWord_2143613, baseEnd_2143613] using wordTrace_append hprefix tailTrace_2143613
  have hstable : (prefixWord ++ tailWord_2143613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143613).length < 2 ^ (prefixWord ++ tailWord_2143613).sum := by decide
  have hdescent : baseEnd_2143613 < baseStart_2143613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143633 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_2143633 : Nat := 118140960795 + 2143633 * 2 ^ 59
def prefixEnd_2143633 : Nat := 4983230072969 + 3 ^ 40 * 2143633 * 2
def baseEnd_2143633 : Nat := 1100714075839516759729117

theorem tailTrace_2143633 : CollatzResearch.WordTrace tailWord_2143633 prefixEnd_2143633 1100714075839516759729117 := by
  unfold tailWord_2143633
  simp only [CollatzResearch.WordTrace]
  refine ⟨78184718642991219214531553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52123145761994146143021035 78184718642991219214531553)
  ·
    refine ⟨58638538982243414410898665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78184718642991219214531553 58638538982243414410898665)
    ·
      refine ⟨43978904236682560808173999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58638538982243414410898665 43978904236682560808173999)
      ·
        refine ⟨65968356355023841212260999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43978904236682560808173999 65968356355023841212260999)
        ·
          refine ⟨98952534532535761818391499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65968356355023841212260999 98952534532535761818391499)
          ·
            refine ⟨148428801798803642727587249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98952534532535761818391499 148428801798803642727587249)
            ·
              refine ⟨111321601349102732045690437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148428801798803642727587249 111321601349102732045690437)
              ·
                refine ⟨20872800252956762258566957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111321601349102732045690437 20872800252956762258566957)
                ·
                  refine ⟨7827300094858785846962609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20872800252956762258566957 7827300094858785846962609)
                  ·
                    refine ⟨5870475071144089385221957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7827300094858785846962609 5870475071144089385221957)
                    ·
                      refine ⟨1100714075839516759729117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5870475071144089385221957 1100714075839516759729117)
                      ·
                        rfl

theorem cell23_2143633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_2143633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143633 prefixEnd_2143633 := by exact prefixLift 2143633
  have htrace : WordTrace (prefixWord ++ tailWord_2143633) baseStart_2143633 baseEnd_2143633 := by
    simpa [prefixWord, tailWord_2143633, baseEnd_2143633] using wordTrace_append hprefix tailTrace_2143633
  have hstable : (prefixWord ++ tailWord_2143633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143633).length < 2 ^ (prefixWord ++ tailWord_2143633).sum := by decide
  have hdescent : baseEnd_2143633 < baseStart_2143633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143647 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 2, 4]
def baseStart_2143647 : Nat := 118140960795 + 2143647 * 2 ^ 59
def prefixEnd_2143647 : Nat := 4983230072969 + 3 ^ 40 * 2143647 * 2
def baseEnd_2143647 : Nat := 366907088189559901651351

theorem tailTrace_2143647 : CollatzResearch.WordTrace tailWord_2143647 prefixEnd_2143647 366907088189559901651351 := by
  unfold tailWord_2143647
  simp only [CollatzResearch.WordTrace]
  refine ⟨78185229264940499605541195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52123486176626999737027463 78185229264940499605541195)
  ·
    refine ⟨117277843897410749408311793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78185229264940499605541195 117277843897410749408311793)
    ·
      refine ⟨87958382923058062056233845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117277843897410749408311793 87958382923058062056233845)
      ·
        refine ⟨8246098399036693317771923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87958382923058062056233845 8246098399036693317771923)
        ·
          refine ⟨12369147598555039976657885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8246098399036693317771923 12369147598555039976657885)
          ·
            refine ⟨4638430349458139991246707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12369147598555039976657885 4638430349458139991246707)
            ·
              refine ⟨6957645524187209986870061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638430349458139991246707 6957645524187209986870061)
              ·
                refine ⟨2609117071570203745076273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6957645524187209986870061 2609117071570203745076273)
                ·
                  refine ⟨1956837803677652808807205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609117071570203745076273 1956837803677652808807205)
                  ·
                    refine ⟨366907088189559901651351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1956837803677652808807205 366907088189559901651351)
                    ·
                      rfl

theorem cell23_2143647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_2143647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143647 prefixEnd_2143647 := by exact prefixLift 2143647
  have htrace : WordTrace (prefixWord ++ tailWord_2143647) baseStart_2143647 baseEnd_2143647 := by
    simpa [prefixWord, tailWord_2143647, baseEnd_2143647] using wordTrace_append hprefix tailTrace_2143647
  have hstable : (prefixWord ++ tailWord_2143647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143647).length < 2 ^ (prefixWord ++ tailWord_2143647).sum := by decide
  have hdescent : baseEnd_2143647 < baseStart_2143647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143650 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2143650 : Nat := 118140960795 + 2143650 * 2 ^ 59
def prefixEnd_2143650 : Nat := 4983230072969 + 3 ^ 40 * 2143650 * 2
def baseEnd_2143650 : Nat := 1100722805010643193216539

theorem tailTrace_2143650 : CollatzResearch.WordTrace tailWord_2143650 prefixEnd_2143650 1100722805010643193216539 := by
  unfold tailWord_2143650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19546334670982407779475101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52123559122619754078600269 19546334670982407779475101)
  ·
    refine ⟨7329875501618402917303163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19546334670982407779475101 7329875501618402917303163)
    ·
      refine ⟨10994813252427604375954745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329875501618402917303163 10994813252427604375954745)
      ·
        refine ⟨8246109939320703281966059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10994813252427604375954745 8246109939320703281966059)
        ·
          refine ⟨12369164908981054922949089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8246109939320703281966059 12369164908981054922949089)
          ·
            refine ⟨9276873681735791192211817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12369164908981054922949089 9276873681735791192211817)
            ·
              refine ⟨6957655261301843394158863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9276873681735791192211817 6957655261301843394158863)
              ·
                refine ⟨10436482891952765091238295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6957655261301843394158863 10436482891952765091238295)
                ·
                  refine ⟨15654724337929147636857443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10436482891952765091238295 15654724337929147636857443)
                  ·
                    refine ⟨23482086506893721455286165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15654724337929147636857443 23482086506893721455286165)
                    ·
                      refine ⟨1100722805010643193216539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23482086506893721455286165 1100722805010643193216539)
                      ·
                        rfl

theorem cell23_2143650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2143650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143650 prefixEnd_2143650 := by exact prefixLift 2143650
  have htrace : WordTrace (prefixWord ++ tailWord_2143650) baseStart_2143650 baseEnd_2143650 := by
    simpa [prefixWord, tailWord_2143650, baseEnd_2143650] using wordTrace_append hprefix tailTrace_2143650
  have hstable : (prefixWord ++ tailWord_2143650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143650).length < 2 ^ (prefixWord ++ tailWord_2143650).sum := by decide
  have hdescent : baseEnd_2143650 < baseStart_2143650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143682 : List Nat := [3, 5, 2, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2143682 : Nat := 118140960795 + 2143682 * 2 ^ 59
def prefixEnd_2143682 : Nat := 4983230072969 + 3 ^ 40 * 2143682 * 2
def baseEnd_2143682 : Nat := 1100739236391587068016393

theorem tailTrace_2143682 : CollatzResearch.WordTrace tailWord_2143682 prefixEnd_2143682 1100739236391587068016393 := by
  unfold tailWord_2143682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19546626454953425145766325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52124337213209133722043533 19546626454953425145766325)
  ·
    refine ⟨1832496230151883607415593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19546626454953425145766325 1832496230151883607415593)
    ·
      refine ⟨1374372172613912705561695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1832496230151883607415593 1374372172613912705561695)
      ·
        refine ⟨2061558258920869058342543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374372172613912705561695 2061558258920869058342543)
        ·
          refine ⟨3092337388381303587513815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061558258920869058342543 3092337388381303587513815)
          ·
            refine ⟨4638506082571955381270723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092337388381303587513815 4638506082571955381270723)
            ·
              refine ⟨6957759123857933071906085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638506082571955381270723 6957759123857933071906085)
              ·
                refine ⟨1304579835723362450982391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6957759123857933071906085 1304579835723362450982391)
                ·
                  refine ⟨1956869753585043676473587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1304579835723362450982391 1956869753585043676473587)
                  ·
                    refine ⟨2935304630377565514710381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1956869753585043676473587 2935304630377565514710381)
                    ·
                      refine ⟨1100739236391587068016393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2935304630377565514710381 1100739236391587068016393)
                      ·
                        rfl

theorem cell23_2143682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2143682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143682 prefixEnd_2143682 := by exact prefixLift 2143682
  have htrace : WordTrace (prefixWord ++ tailWord_2143682) baseStart_2143682 baseEnd_2143682 := by
    simpa [prefixWord, tailWord_2143682, baseEnd_2143682] using wordTrace_append hprefix tailTrace_2143682
  have hstable : (prefixWord ++ tailWord_2143682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143682).length < 2 ^ (prefixWord ++ tailWord_2143682).sum := by decide
  have hdescent : baseEnd_2143682 < baseStart_2143682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143683 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5]
def baseStart_2143683 : Nat := 118140960795 + 2143683 * 2 ^ 59
def prefixEnd_2143683 : Nat := 4983230072969 + 3 ^ 40 * 2143683 * 2
def baseEnd_2143683 : Nat := 1100739749872241564103887

theorem tailTrace_2143683 : CollatzResearch.WordTrace tailWord_2143683 prefixEnd_2143683 1100739749872241564103887 := by
  unfold tailWord_2143683
  simp only [CollatzResearch.WordTrace]
  refine ⟨78186542292810077753851703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52124361528540051835901135 78186542292810077753851703)
  ·
    refine ⟨117279813439215116630777555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78186542292810077753851703 117279813439215116630777555)
    ·
      refine ⟨175919720158822674946166333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117279813439215116630777555 175919720158822674946166333)
      ·
        refine ⟨65969895059558503104812375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175919720158822674946166333 65969895059558503104812375)
        ·
          refine ⟨98954842589337754657218563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65969895059558503104812375 98954842589337754657218563)
          ·
            refine ⟨148432263884006631985827845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98954842589337754657218563 148432263884006631985827845)
            ·
              refine ⟨27831049478251243497342721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148432263884006631985827845 27831049478251243497342721)
              ·
                refine ⟨20873287108688432623007041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27831049478251243497342721 20873287108688432623007041)
                ·
                  refine ⟨15654965331516324467255281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20873287108688432623007041 15654965331516324467255281)
                  ·
                    refine ⟨11741223998637243350441461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15654965331516324467255281 11741223998637243350441461)
                    ·
                      refine ⟨1100739749872241564103887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11741223998637243350441461 1100739749872241564103887)
                      ·
                        rfl

theorem cell23_2143683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_2143683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143683 prefixEnd_2143683 := by exact prefixLift 2143683
  have htrace : WordTrace (prefixWord ++ tailWord_2143683) baseStart_2143683 baseEnd_2143683 := by
    simpa [prefixWord, tailWord_2143683, baseEnd_2143683] using wordTrace_append hprefix tailTrace_2143683
  have hstable : (prefixWord ++ tailWord_2143683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143683).length < 2 ^ (prefixWord ++ tailWord_2143683).sum := by decide
  have hdescent : baseEnd_2143683 < baseStart_2143683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143727 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 1, 4, 2]
def baseStart_2143727 : Nat := 118140960795 + 2143727 * 2 ^ 59
def prefixEnd_2143727 : Nat := 4983230072969 + 3 ^ 40 * 2143727 * 2
def baseEnd_2143727 : Nat := 1100762343021039391953685

theorem tailTrace_2143727 : CollatzResearch.WordTrace tailWord_2143727 prefixEnd_2143727 1100762343021039391953685 := by
  unfold tailWord_2143727
  simp only [CollatzResearch.WordTrace]
  refine ⟨78188147104650673268453435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52125431403100448845635623 78188147104650673268453435)
  ·
    refine ⟨117282220656976009902680153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78188147104650673268453435 117282220656976009902680153)
    ·
      refine ⟨87961665492732007427010115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117282220656976009902680153 87961665492732007427010115)
      ·
        refine ⟨131942498239098011140515173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87961665492732007427010115 131942498239098011140515173)
        ·
          refine ⟨24739218419830877088846595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 131942498239098011140515173 24739218419830877088846595)
          ·
            refine ⟨37108827629746315633269893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24739218419830877088846595 37108827629746315633269893)
            ·
              refine ⟨6957905180577434181238105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37108827629746315633269893 6957905180577434181238105)
              ·
                refine ⟨5218428885433075635928579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6957905180577434181238105 5218428885433075635928579)
                ·
                  refine ⟨7827643328149613453892869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218428885433075635928579 7827643328149613453892869)
                  ·
                    refine ⟨1467683124028052522604913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7827643328149613453892869 1467683124028052522604913)
                    ·
                      refine ⟨1100762343021039391953685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467683124028052522604913 1100762343021039391953685)
                      ·
                        rfl

theorem cell23_2143727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4, 2].length) (baseStart_2143727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143727 prefixEnd_2143727 := by exact prefixLift 2143727
  have htrace : WordTrace (prefixWord ++ tailWord_2143727) baseStart_2143727 baseEnd_2143727 := by
    simpa [prefixWord, tailWord_2143727, baseEnd_2143727] using wordTrace_append hprefix tailTrace_2143727
  have hstable : (prefixWord ++ tailWord_2143727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143727).length < 2 ^ (prefixWord ++ tailWord_2143727).sum := by decide
  have hdescent : baseEnd_2143727 < baseStart_2143727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143740 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_2143740 : Nat := 118140960795 + 2143740 * 2 ^ 59
def prefixEnd_2143740 : Nat := 4983230072969 + 3 ^ 40 * 2143740 * 2
def baseEnd_2143740 : Nat := 1100769018269547841091125

theorem tailTrace_2143740 : CollatzResearch.WordTrace tailWord_2143740 prefixEnd_2143740 1100769018269547841091125 := by
  unfold tailWord_2143740
  simp only [CollatzResearch.WordTrace]
  refine ⟨39094310626801788244338337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52125747502402384325784449 39094310626801788244338337)
  ·
    refine ⟨29320732970101341183253753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39094310626801788244338337 29320732970101341183253753)
    ·
      refine ⟨21990549727576005887440315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29320732970101341183253753 21990549727576005887440315)
      ·
        refine ⟨32985824591364008831160473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21990549727576005887440315 32985824591364008831160473)
        ·
          refine ⟨24739368443523006623370355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32985824591364008831160473 24739368443523006623370355)
          ·
            refine ⟨37109052665284509935055533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24739368443523006623370355 37109052665284509935055533)
            ·
              refine ⟨13915894749481691225645825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37109052665284509935055533 13915894749481691225645825)
              ·
                refine ⟨10436921062111268419234369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13915894749481691225645825 10436921062111268419234369)
                ·
                  refine ⟨7827690796583451314425777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10436921062111268419234369 7827690796583451314425777)
                  ·
                    refine ⟨5870768097437588485819333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7827690796583451314425777 5870768097437588485819333)
                    ·
                      refine ⟨1100769018269547841091125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5870768097437588485819333 1100769018269547841091125)
                      ·
                        rfl

theorem cell23_2143740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_2143740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143740 prefixEnd_2143740 := by exact prefixLift 2143740
  have htrace : WordTrace (prefixWord ++ tailWord_2143740) baseStart_2143740 baseEnd_2143740 := by
    simpa [prefixWord, tailWord_2143740, baseEnd_2143740] using wordTrace_append hprefix tailTrace_2143740
  have hstable : (prefixWord ++ tailWord_2143740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143740).length < 2 ^ (prefixWord ++ tailWord_2143740).sum := by decide
  have hdescent : baseEnd_2143740 < baseStart_2143740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143743 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_2143743 : Nat := 118140960795 + 2143743 * 2 ^ 59
def prefixEnd_2143743 : Nat := 4983230072969 + 3 ^ 40 * 2143743 * 2
def baseEnd_2143743 : Nat := 1100770558711511329353611

theorem tailTrace_2143743 : CollatzResearch.WordTrace tailWord_2143743 prefixEnd_2143743 1100770558711511329353611 := by
  unfold tailWord_2143743
  simp only [CollatzResearch.WordTrace]
  refine ⟨78188730672592708001035883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52125820448395138667357255 78188730672592708001035883)
  ·
    refine ⟨117283096008889062001553825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78188730672592708001035883 117283096008889062001553825)
    ·
      refine ⟨87962322006666796501165369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117283096008889062001553825 87962322006666796501165369)
      ·
        refine ⟨65971741505000097375874027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87962322006666796501165369 65971741505000097375874027)
        ·
          refine ⟨98957612257500146063811041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65971741505000097375874027 98957612257500146063811041)
          ·
            refine ⟨74218209193125109547858281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98957612257500146063811041 74218209193125109547858281)
            ·
              refine ⟨55663656894843832160893711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74218209193125109547858281 55663656894843832160893711)
              ·
                refine ⟨83495485342265748241340567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55663656894843832160893711 83495485342265748241340567)
                ·
                  refine ⟨125243228013398622362010851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83495485342265748241340567 125243228013398622362010851)
                  ·
                    refine ⟨187864842020097933543016277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125243228013398622362010851 187864842020097933543016277)
                    ·
                      refine ⟨1100770558711511329353611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 187864842020097933543016277 1100770558711511329353611)
                      ·
                        rfl

theorem cell23_2143743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_2143743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143743 prefixEnd_2143743 := by exact prefixLift 2143743
  have htrace : WordTrace (prefixWord ++ tailWord_2143743) baseStart_2143743 baseEnd_2143743 := by
    simpa [prefixWord, tailWord_2143743, baseEnd_2143743] using wordTrace_append hprefix tailTrace_2143743
  have hstable : (prefixWord ++ tailWord_2143743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143743).length < 2 ^ (prefixWord ++ tailWord_2143743).sum := by decide
  have hdescent : baseEnd_2143743 < baseStart_2143743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143761 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 2, 2, 2]
def baseStart_2143761 : Nat := 118140960795 + 2143761 * 2 ^ 59
def prefixEnd_2143761 : Nat := 4983230072969 + 3 ^ 40 * 2143761 * 2
def baseEnd_2143761 : Nat := 1100779801363292258928529

theorem tailTrace_2143761 : CollatzResearch.WordTrace tailWord_2143761 prefixEnd_2143761 1100779801363292258928529 := by
  unfold tailWord_2143761
  simp only [CollatzResearch.WordTrace]
  refine ⟨78189387186527497075191137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52126258124351664716794091 78189387186527497075191137)
  ·
    refine ⟨58642040389895622806393353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78189387186527497075191137 58642040389895622806393353)
    ·
      refine ⟨43981530292421717104795015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58642040389895622806393353 43981530292421717104795015)
      ·
        refine ⟨65972295438632575657192523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43981530292421717104795015 65972295438632575657192523)
        ·
          refine ⟨98958443157948863485788785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65972295438632575657192523 98958443157948863485788785)
          ·
            refine ⟨74218832368461647614341589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98958443157948863485788785 74218832368461647614341589)
            ·
              refine ⟨1739503883635819865961131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74218832368461647614341589 1739503883635819865961131)
              ·
                refine ⟨2609255825453729798941697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739503883635819865961131 2609255825453729798941697)
                ·
                  refine ⟨1956941869090297349206273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609255825453729798941697 1956941869090297349206273)
                  ·
                    refine ⟨1467706401817723011904705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1956941869090297349206273 1467706401817723011904705)
                    ·
                      refine ⟨1100779801363292258928529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467706401817723011904705 1100779801363292258928529)
                      ·
                        rfl

theorem cell23_2143761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_2143761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143761 prefixEnd_2143761 := by exact prefixLift 2143761
  have htrace : WordTrace (prefixWord ++ tailWord_2143761) baseStart_2143761 baseEnd_2143761 := by
    simpa [prefixWord, tailWord_2143761, baseEnd_2143761] using wordTrace_append hprefix tailTrace_2143761
  have hstable : (prefixWord ++ tailWord_2143761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143761).length < 2 ^ (prefixWord ++ tailWord_2143761).sum := by decide
  have hdescent : baseEnd_2143761 < baseStart_2143761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143797 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2143797 : Nat := 118140960795 + 2143797 * 2 ^ 59
def prefixEnd_2143797 : Nat := 4983230072969 + 3 ^ 40 * 2143797 * 2
def baseEnd_2143797 : Nat := 366932762222284706026121

theorem tailTrace_2143797 : CollatzResearch.WordTrace tailWord_2143797 prefixEnd_2143797 366932762222284706026121 := by
  unfold tailWord_2143797
  simp only [CollatzResearch.WordTrace]
  refine ⟨78190700214397075223501645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52127133476264716815667763 78190700214397075223501645)
  ·
    refine ⟨29321512580398903208813117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78190700214397075223501645 29321512580398903208813117)
    ·
      refine ⟨10995567217649588703304919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29321512580398903208813117 10995567217649588703304919)
      ·
        refine ⟨16493350826474383054957379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10995567217649588703304919 16493350826474383054957379)
        ·
          refine ⟨24740026239711574582436069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16493350826474383054957379 24740026239711574582436069)
          ·
            refine ⟨4638754919945920234206763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24740026239711574582436069 4638754919945920234206763)
            ·
              refine ⟨6958132379918880351310145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638754919945920234206763 6958132379918880351310145)
              ·
                refine ⟨5218599284939160263482609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6958132379918880351310145 5218599284939160263482609)
                ·
                  refine ⟨3913949463704370197611957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5218599284939160263482609 3913949463704370197611957)
                  ·
                    refine ⟨366932762222284706026121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3913949463704370197611957 366932762222284706026121)
                    ·
                      rfl

theorem cell23_2143797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2143797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143797 prefixEnd_2143797 := by exact prefixLift 2143797
  have htrace : WordTrace (prefixWord ++ tailWord_2143797) baseStart_2143797 baseEnd_2143797 := by
    simpa [prefixWord, tailWord_2143797, baseEnd_2143797] using wordTrace_append hprefix tailTrace_2143797
  have hstable : (prefixWord ++ tailWord_2143797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143797).length < 2 ^ (prefixWord ++ tailWord_2143797).sum := by decide
  have hdescent : baseEnd_2143797 < baseStart_2143797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143817 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 2, 4, 2]
def baseStart_2143817 : Nat := 118140960795 + 2143817 * 2 ^ 59
def prefixEnd_2143817 : Nat := 4983230072969 + 3 ^ 40 * 2143817 * 2
def baseEnd_2143817 : Nat := 1100808556279944039828271

theorem tailTrace_2143817 : CollatzResearch.WordTrace tailWord_2143817 prefixEnd_2143817 1100808556279944039828271 := by
  unfold tailWord_2143817
  simp only [CollatzResearch.WordTrace]
  refine ⟨78191429674324618639229705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52127619782883079092819803 78191429674324618639229705)
  ·
    refine ⟨58643572255743463979422279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78191429674324618639229705 58643572255743463979422279)
    ·
      refine ⟨87965358383615195969133419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58643572255743463979422279 87965358383615195969133419)
      ·
        refine ⟨131948037575422793953700129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87965358383615195969133419 131948037575422793953700129)
        ·
          refine ⟨98961028181567095465275097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131948037575422793953700129 98961028181567095465275097)
          ·
            refine ⟨74220771136175321598956323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98961028181567095465275097 74220771136175321598956323)
            ·
              refine ⟨111331156704262982398434485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74220771136175321598956323 111331156704262982398434485)
              ·
                refine ⟨10437295941024654599853233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111331156704262982398434485 10437295941024654599853233)
                ·
                  refine ⟨7827971955768490949889925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10437295941024654599853233 7827971955768490949889925)
                  ·
                    refine ⟨1467744741706592053104361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7827971955768490949889925 1467744741706592053104361)
                    ·
                      refine ⟨1100808556279944039828271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1467744741706592053104361 1100808556279944039828271)
                      ·
                        rfl

theorem cell23_2143817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 4, 2].length) (baseStart_2143817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143817 prefixEnd_2143817 := by exact prefixLift 2143817
  have htrace : WordTrace (prefixWord ++ tailWord_2143817) baseStart_2143817 baseEnd_2143817 := by
    simpa [prefixWord, tailWord_2143817, baseEnd_2143817] using wordTrace_append hprefix tailTrace_2143817
  have hstable : (prefixWord ++ tailWord_2143817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143817).length < 2 ^ (prefixWord ++ tailWord_2143817).sum := by decide
  have hdescent : baseEnd_2143817 < baseStart_2143817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143884 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_2143884 : Nat := 118140960795 + 2143884 * 2 ^ 59
def prefixEnd_2143884 : Nat := 4983230072969 + 3 ^ 40 * 2143884 * 2
def baseEnd_2143884 : Nat := 1100842959483795277690463

theorem tailTrace_2143884 : CollatzResearch.WordTrace tailWord_2143884 prefixEnd_2143884 1100842959483795277690463 := by
  unfold tailWord_2143884
  simp only [CollatzResearch.WordTrace]
  refine ⟨39096936682540944540959353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52129248910054592721279137 39096936682540944540959353)
  ·
    refine ⟨29322702511905708405719515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39096936682540944540959353 29322702511905708405719515)
    ·
      refine ⟨43984053767858562608579273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29322702511905708405719515 43984053767858562608579273)
      ·
        refine ⟨32988040325893921956434455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43984053767858562608579273 32988040325893921956434455)
        ·
          refine ⟨49482060488840882934651683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32988040325893921956434455 49482060488840882934651683)
          ·
            refine ⟨74223090733261324401977525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49482060488840882934651683 74223090733261324401977525)
            ·
              refine ⟨6958414756243249162685393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74223090733261324401977525 6958414756243249162685393)
              ·
                refine ⟨5218811067182436872014045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6958414756243249162685393 5218811067182436872014045)
                ·
                  refine ⟨1957054150193413827005267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5218811067182436872014045 1957054150193413827005267)
                  ·
                    refine ⟨2935581225290120740507901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1957054150193413827005267 2935581225290120740507901)
                    ·
                      refine ⟨1100842959483795277690463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2935581225290120740507901 1100842959483795277690463)
                      ·
                        rfl

theorem cell23_2143884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_2143884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143884 prefixEnd_2143884 := by exact prefixLift 2143884
  have htrace : WordTrace (prefixWord ++ tailWord_2143884) baseStart_2143884 baseEnd_2143884 := by
    simpa [prefixWord, tailWord_2143884, baseEnd_2143884] using wordTrace_append hprefix tailTrace_2143884
  have hstable : (prefixWord ++ tailWord_2143884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143884).length < 2 ^ (prefixWord ++ tailWord_2143884).sum := by decide
  have hdescent : baseEnd_2143884 < baseStart_2143884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143904 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 1, 5]
def baseStart_2143904 : Nat := 118140960795 + 2143904 * 2 ^ 59
def prefixEnd_2143904 : Nat := 4983230072969 + 3 ^ 40 * 2143904 * 2
def baseEnd_2143904 : Nat := 366951076365628399813457

theorem tailTrace_2143904 : CollatzResearch.WordTrace tailWord_2143904 prefixEnd_2143904 366951076365628399813457 := by
  unfold tailWord_2143904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39097301412504716248823383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52129735216672954998431177 39097301412504716248823383)
  ·
    refine ⟨58645952118757074373235075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39097301412504716248823383 58645952118757074373235075)
    ·
      refine ⟨87968928178135611559852613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58645952118757074373235075 87968928178135611559852613)
      ·
        refine ⟨16494174033400427167472365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87968928178135611559852613 16494174033400427167472365)
        ·
          refine ⟨6185315262525160187802137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16494174033400427167472365 6185315262525160187802137)
          ·
            refine ⟨4638986446893870140851603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6185315262525160187802137 4638986446893870140851603)
            ·
              refine ⟨6958479670340805211277405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638986446893870140851603 6958479670340805211277405)
              ·
                refine ⟨2609429876377801954229027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6958479670340805211277405 2609429876377801954229027)
                ·
                  refine ⟨3914144814566702931343541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609429876377801954229027 3914144814566702931343541)
                  ·
                    refine ⟨366951076365628399813457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3914144814566702931343541 366951076365628399813457)
                    ·
                      rfl

theorem cell23_2143904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_2143904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143904 prefixEnd_2143904 := by exact prefixLift 2143904
  have htrace : WordTrace (prefixWord ++ tailWord_2143904) baseStart_2143904 baseEnd_2143904 := by
    simpa [prefixWord, tailWord_2143904, baseEnd_2143904] using wordTrace_append hprefix tailTrace_2143904
  have hstable : (prefixWord ++ tailWord_2143904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143904).length < 2 ^ (prefixWord ++ tailWord_2143904).sum := by decide
  have hdescent : baseEnd_2143904 < baseStart_2143904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143927 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_2143927 : Nat := 118140960795 + 2143927 * 2 ^ 59
def prefixEnd_2143927 : Nat := 4983230072969 + 3 ^ 40 * 2143927 * 2
def baseEnd_2143927 : Nat := 1100865039151938609452765

theorem tailTrace_2143927 : CollatzResearch.WordTrace tailWord_2143927 prefixEnd_2143927 1100865039151938609452765 := by
  unfold tailWord_2143927
  simp only [CollatzResearch.WordTrace]
  refine ⟨78195441703926107425734035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52130294469284071617156023 78195441703926107425734035)
  ·
    refine ⟨117293162555889161138601053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78195441703926107425734035 117293162555889161138601053)
    ·
      refine ⟨43984935958458435426975395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117293162555889161138601053 43984935958458435426975395)
      ·
        refine ⟨65977403937687653140463093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43984935958458435426975395 65977403937687653140463093)
        ·
          refine ⟨6185381619158217481918415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65977403937687653140463093 6185381619158217481918415)
          ·
            refine ⟨9278072428737326222877623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6185381619158217481918415 9278072428737326222877623)
            ·
              refine ⟨13917108643105989334316435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9278072428737326222877623 13917108643105989334316435)
              ·
                refine ⟨20875662964658984001474653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13917108643105989334316435 20875662964658984001474653)
                ·
                  refine ⟨7828373611747119000552995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20875662964658984001474653 7828373611747119000552995)
                  ·
                    refine ⟨11742560417620678500829493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7828373611747119000552995 11742560417620678500829493)
                    ·
                      refine ⟨1100865039151938609452765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11742560417620678500829493 1100865039151938609452765)
                      ·
                        rfl

theorem cell23_2143927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_2143927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143927 prefixEnd_2143927 := by exact prefixLift 2143927
  have htrace : WordTrace (prefixWord ++ tailWord_2143927) baseStart_2143927 baseEnd_2143927 := by
    simpa [prefixWord, tailWord_2143927, baseEnd_2143927] using wordTrace_append hprefix tailTrace_2143927
  have hstable : (prefixWord ++ tailWord_2143927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143927).length < 2 ^ (prefixWord ++ tailWord_2143927).sum := by decide
  have hdescent : baseEnd_2143927 < baseStart_2143927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143934 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2143934 : Nat := 118140960795 + 2143934 * 2 ^ 59
def prefixEnd_2143934 : Nat := 4983230072969 + 3 ^ 40 * 2143934 * 2
def baseEnd_2143934 : Nat := 366956211172173360688411

theorem tailTrace_2143934 : CollatzResearch.WordTrace tailWord_2143934 prefixEnd_2143934 366956211172173360688411 := by
  unfold tailWord_2143934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9774462126862593452654857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52130464676600498414159237 9774462126862593452654857)
  ·
    refine ⟨7330846595146945089491143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9774462126862593452654857 7330846595146945089491143)
    ·
      refine ⟨10996269892720417634236715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7330846595146945089491143 10996269892720417634236715)
      ·
        refine ⟨16494404839080626451355073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10996269892720417634236715 16494404839080626451355073)
        ·
          refine ⟨12370803629310469838516305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16494404839080626451355073 12370803629310469838516305)
          ·
            refine ⟨9278102721982852378887229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12370803629310469838516305 9278102721982852378887229)
            ·
              refine ⟨3479288520743569642082711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9278102721982852378887229 3479288520743569642082711)
              ·
                refine ⟨5218932781115354463124067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479288520743569642082711 5218932781115354463124067)
                ·
                  refine ⟨7828399171673031694686101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5218932781115354463124067 7828399171673031694686101)
                  ·
                    refine ⟨366956211172173360688411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7828399171673031694686101 366956211172173360688411)
                    ·
                      rfl

theorem cell23_2143934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2143934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143934 prefixEnd_2143934 := by exact prefixLift 2143934
  have htrace : WordTrace (prefixWord ++ tailWord_2143934) baseStart_2143934 baseEnd_2143934 := by
    simpa [prefixWord, tailWord_2143934, baseEnd_2143934] using wordTrace_append hprefix tailTrace_2143934
  have hstable : (prefixWord ++ tailWord_2143934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143934).length < 2 ^ (prefixWord ++ tailWord_2143934).sum := by decide
  have hdescent : baseEnd_2143934 < baseStart_2143934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2143997 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2143997 : Nat := 118140960795 + 2143997 * 2 ^ 59
def prefixEnd_2143997 : Nat := 4983230072969 + 3 ^ 40 * 2143997 * 2
def baseEnd_2143997 : Nat := 1100900982797753335577443

theorem tailTrace_2143997 : CollatzResearch.WordTrace tailWord_2143997 prefixEnd_2143997 1100900982797753335577443 := by
  unfold tailWord_2143997
  simp only [CollatzResearch.WordTrace]
  refine ⟨78197994813672509380782245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52131996542448339587188163 78197994813672509380782245)
  ·
    refine ⟨14662124027563595508896671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78197994813672509380782245 14662124027563595508896671)
    ·
      refine ⟨21993186041345393263345007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14662124027563595508896671 21993186041345393263345007)
      ·
        refine ⟨32989779062018089895017511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21993186041345393263345007 32989779062018089895017511)
        ·
          refine ⟨49484668593027134842526267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32989779062018089895017511 49484668593027134842526267)
          ·
            refine ⟨74227002889540702263789401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49484668593027134842526267 74227002889540702263789401)
            ·
              refine ⟨55670252167155526697842051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74227002889540702263789401 55670252167155526697842051)
              ·
                refine ⟨83505378250733290046763077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55670252167155526697842051 83505378250733290046763077)
                ·
                  refine ⟨15657258422012491883768077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83505378250733290046763077 15657258422012491883768077)
                  ·
                    refine ⟨5871471908254684456413029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15657258422012491883768077 5871471908254684456413029)
                    ·
                      refine ⟨1100900982797753335577443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5871471908254684456413029 1100900982797753335577443)
                      ·
                        rfl

theorem cell23_2143997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2143997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2143997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2143997 prefixEnd_2143997 := by exact prefixLift 2143997
  have htrace : WordTrace (prefixWord ++ tailWord_2143997) baseStart_2143997 baseEnd_2143997 := by
    simpa [prefixWord, tailWord_2143997, baseEnd_2143997] using wordTrace_append hprefix tailTrace_2143997
  have hstable : (prefixWord ++ tailWord_2143997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2143997).length < 2 ^ (prefixWord ++ tailWord_2143997).sum := by decide
  have hdescent : baseEnd_2143997 < baseStart_2143997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2143997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144027 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4]
def baseStart_2144027 : Nat := 118140960795 + 2144027 * 2 ^ 59
def prefixEnd_2144027 : Nat := 4983230072969 + 3 ^ 40 * 2144027 * 2
def baseEnd_2144027 : Nat := 1100916387217388218202305

theorem tailTrace_2144027 : CollatzResearch.WordTrace tailWord_2144027 prefixEnd_2144027 1100916387217388218202305 := by
  unfold tailWord_2144027
  simp only [CollatzResearch.WordTrace]
  refine ⟨78199089003563824504374335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52132726002375883002916223 78199089003563824504374335)
  ·
    refine ⟨117298633505345736756561503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78199089003563824504374335 117298633505345736756561503)
    ·
      refine ⟨175947950258018605134842255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117298633505345736756561503 175947950258018605134842255)
      ·
        refine ⟨263921925387027907702263383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175947950258018605134842255 263921925387027907702263383)
        ·
          refine ⟨395882888080541861553395075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263921925387027907702263383 395882888080541861553395075)
          ·
            refine ⟨593824332120812792330092613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395882888080541861553395075 593824332120812792330092613)
            ·
              refine ⟨111342062272652398561892365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 593824332120812792330092613 111342062272652398561892365)
              ·
                refine ⟨41753273352244649460709637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111342062272652398561892365 41753273352244649460709637)
                ·
                  refine ⟨7828738753545871773883057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41753273352244649460709637 7828738753545871773883057)
                  ·
                    refine ⟨5871554065159403830412293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7828738753545871773883057 5871554065159403830412293)
                    ·
                      refine ⟨1100916387217388218202305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5871554065159403830412293 1100916387217388218202305)
                      ·
                        rfl

theorem cell23_2144027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_2144027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144027 prefixEnd_2144027 := by exact prefixLift 2144027
  have htrace : WordTrace (prefixWord ++ tailWord_2144027) baseStart_2144027 baseEnd_2144027 := by
    simpa [prefixWord, tailWord_2144027, baseEnd_2144027] using wordTrace_append hprefix tailTrace_2144027
  have hstable : (prefixWord ++ tailWord_2144027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144027).length < 2 ^ (prefixWord ++ tailWord_2144027).sum := by decide
  have hdescent : baseEnd_2144027 < baseStart_2144027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144034 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2144034 : Nat := 118140960795 + 2144034 * 2 ^ 59
def prefixEnd_2144034 : Nat := 4983230072969 + 3 ^ 40 * 2144034 * 2
def baseEnd_2144034 : Nat := 1100919981581969690814773

theorem tailTrace_2144034 : CollatzResearch.WordTrace tailWord_2144034 prefixEnd_2144034 1100919981581969690814773 := by
  unfold tailWord_2144034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19549836078634616174969789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52132896209692309799919437 19549836078634616174969789)
  ·
    refine ⟨7331188529487981065613671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19549836078634616174969789 7331188529487981065613671)
    ·
      refine ⟨10996782794231971598420507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7331188529487981065613671 10996782794231971598420507)
      ·
        refine ⟨16495174191347957397630761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10996782794231971598420507 16495174191347957397630761)
        ·
          refine ⟨12371380643510968048223071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16495174191347957397630761 12371380643510968048223071)
          ·
            refine ⟨18557070965266452072334607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12371380643510968048223071 18557070965266452072334607)
            ·
              refine ⟨27835606447899678108501911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18557070965266452072334607 27835606447899678108501911)
              ·
                refine ⟨41753409671849517162752867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27835606447899678108501911 41753409671849517162752867)
                ·
                  refine ⟨62630114507774275744129301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41753409671849517162752867 62630114507774275744129301)
                  ·
                    refine ⟨2935786617551919175506061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62630114507774275744129301 2935786617551919175506061)
                    ·
                      refine ⟨1100919981581969690814773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2935786617551919175506061 1100919981581969690814773)
                      ·
                        rfl

theorem cell23_2144034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2144034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144034 prefixEnd_2144034 := by exact prefixLift 2144034
  have htrace : WordTrace (prefixWord ++ tailWord_2144034) baseStart_2144034 baseEnd_2144034 := by
    simpa [prefixWord, tailWord_2144034, baseEnd_2144034] using wordTrace_append hprefix tailTrace_2144034
  have hstable : (prefixWord ++ tailWord_2144034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144034).length < 2 ^ (prefixWord ++ tailWord_2144034).sum := by decide
  have hdescent : baseEnd_2144034 < baseStart_2144034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144044 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_2144044 : Nat := 118140960795 + 2144044 * 2 ^ 59
def prefixEnd_2144044 : Nat := 4983230072969 + 3 ^ 40 * 2144044 * 2
def baseEnd_2144044 : Nat := 1100925116388514651689727

theorem tailTrace_2144044 : CollatzResearch.WordTrace tailWord_2144044 prefixEnd_2144044 1100925116388514651689727 := by
  unfold tailWord_2144044
  simp only [CollatzResearch.WordTrace]
  refine ⟨39099854522251118203871593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52133139363001490938495457 39099854522251118203871593)
  ·
    refine ⟨29324890891688338652903695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39099854522251118203871593 29324890891688338652903695)
    ·
      refine ⟨43987336337532507979355543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29324890891688338652903695 43987336337532507979355543)
      ·
        refine ⟨65981004506298761969033315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43987336337532507979355543 65981004506298761969033315)
        ·
          refine ⟨98971506759448142953549973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65981004506298761969033315 98971506759448142953549973)
          ·
            refine ⟨4639289379349131700947655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98971506759448142953549973 4639289379349131700947655)
            ·
              refine ⟨6958934069023697551421483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639289379349131700947655 6958934069023697551421483)
              ·
                refine ⟨10438401103535546327132225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6958934069023697551421483 10438401103535546327132225)
                ·
                  refine ⟨7828800827651659745349169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10438401103535546327132225 7828800827651659745349169)
                  ·
                    refine ⟨5871600620738744809011877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7828800827651659745349169 5871600620738744809011877)
                    ·
                      refine ⟨1100925116388514651689727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5871600620738744809011877 1100925116388514651689727)
                      ·
                        rfl

theorem cell23_2144044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_2144044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144044 prefixEnd_2144044 := by exact prefixLift 2144044
  have htrace : WordTrace (prefixWord ++ tailWord_2144044) baseStart_2144044 baseEnd_2144044 := by
    simpa [prefixWord, tailWord_2144044, baseEnd_2144044] using wordTrace_append hprefix tailTrace_2144044
  have hstable : (prefixWord ++ tailWord_2144044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144044).length < 2 ^ (prefixWord ++ tailWord_2144044).sum := by decide
  have hdescent : baseEnd_2144044 < baseStart_2144044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144104 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2144104 : Nat := 118140960795 + 2144104 * 2 ^ 59
def prefixEnd_2144104 : Nat := 4983230072969 + 3 ^ 40 * 2144104 * 2
def baseEnd_2144104 : Nat := 1100955925227784416939451

theorem tailTrace_2144104 : CollatzResearch.WordTrace tailWord_2144104 prefixEnd_2144104 1100955925227784416939451 := by
  unfold tailWord_2144104
  simp only [CollatzResearch.WordTrace]
  refine ⟨39100948712142433327463683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52134598282856577769951577 39100948712142433327463683)
  ·
    refine ⟨58651423068213649991195525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39100948712142433327463683 58651423068213649991195525)
    ·
      refine ⟨10997141825290059373349161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58651423068213649991195525 10997141825290059373349161)
      ·
        refine ⟨8247856368967544530011871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10997141825290059373349161 8247856368967544530011871)
        ·
          refine ⟨12371784553451316795017807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8247856368967544530011871 12371784553451316795017807)
          ·
            refine ⟨18557676830176975192526711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12371784553451316795017807 18557676830176975192526711)
            ·
              refine ⟨27836515245265462788790067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18557676830176975192526711 27836515245265462788790067)
              ·
                refine ⟨41754772867898194183185101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27836515245265462788790067 41754772867898194183185101)
                ·
                  refine ⟨15658039825461822818694413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41754772867898194183185101 15658039825461822818694413)
                  ·
                    refine ⟨5871764934548183557010405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15658039825461822818694413 5871764934548183557010405)
                    ·
                      refine ⟨1100955925227784416939451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5871764934548183557010405 1100955925227784416939451)
                      ·
                        rfl

theorem cell23_2144104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2144104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144104 prefixEnd_2144104 := by exact prefixLift 2144104
  have htrace : WordTrace (prefixWord ++ tailWord_2144104) baseStart_2144104 baseEnd_2144104 := by
    simpa [prefixWord, tailWord_2144104, baseEnd_2144104] using wordTrace_append hprefix tailTrace_2144104
  have hstable : (prefixWord ++ tailWord_2144104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144104).length < 2 ^ (prefixWord ++ tailWord_2144104).sum := by decide
  have hdescent : baseEnd_2144104 < baseStart_2144104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144138 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2144138 : Nat := 118140960795 + 2144138 * 2 ^ 59
def prefixEnd_2144138 : Nat := 4983230072969 + 3 ^ 40 * 2144138 * 2
def baseEnd_2144138 : Nat := 1100973383570037283914295

theorem tailTrace_2144138 : CollatzResearch.WordTrace tailWord_2144138 prefixEnd_2144138 1100973383570037283914295 := by
  unfold tailWord_2144138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19550784376540422615416267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52135425004107793641110045 19550784376540422615416267)
  ·
    refine ⟨29326176564810633923124401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19550784376540422615416267 29326176564810633923124401)
    ·
      refine ⟨21994632423607975442343301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29326176564810633923124401 21994632423607975442343301)
      ·
        refine ⟨4123993579426495395439369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21994632423607975442343301 4123993579426495395439369)
        ·
          refine ⟨3092995184569871546579527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4123993579426495395439369 3092995184569871546579527)
          ·
            refine ⟨4639492776854807319869291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092995184569871546579527 4639492776854807319869291)
            ·
              refine ⟨6959239165282210979803937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639492776854807319869291 6959239165282210979803937)
              ·
                refine ⟨5219429373961658234852953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6959239165282210979803937 5219429373961658234852953)
                ·
                  refine ⟨3914572030471243676139715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5219429373961658234852953 3914572030471243676139715)
                  ·
                    refine ⟨5871858045706865514209573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3914572030471243676139715 5871858045706865514209573)
                    ·
                      refine ⟨1100973383570037283914295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5871858045706865514209573 1100973383570037283914295)
                      ·
                        rfl

theorem cell23_2144138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2144138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144138 prefixEnd_2144138 := by exact prefixLift 2144138
  have htrace : WordTrace (prefixWord ++ tailWord_2144138) baseStart_2144138 baseEnd_2144138 := by
    simpa [prefixWord, tailWord_2144138, baseEnd_2144138] using wordTrace_append hprefix tailTrace_2144138
  have hstable : (prefixWord ++ tailWord_2144138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144138).length < 2 ^ (prefixWord ++ tailWord_2144138).sum := by decide
  have hdescent : baseEnd_2144138 < baseStart_2144138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144148 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2144148 : Nat := 118140960795 + 2144148 * 2 ^ 59
def prefixEnd_2144148 : Nat := 4983230072969 + 3 ^ 40 * 2144148 * 2
def baseEnd_2144148 : Nat := 366992839458860748263083

theorem tailTrace_2144148 : CollatzResearch.WordTrace tailWord_2144148 prefixEnd_2144148 366992839458860748263083 := by
  unfold tailWord_2144148
  simp only [CollatzResearch.WordTrace]
  refine ⟨39101751118062731084764549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52135668157416974779686065 39101751118062731084764549)
  ·
    refine ⟨7331578334636762078393353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39101751118062731084764549 7331578334636762078393353)
    ·
      refine ⟨5498683750977571558795015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7331578334636762078393353 5498683750977571558795015)
      ·
        refine ⟨8248025626466357338192523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498683750977571558795015 8248025626466357338192523)
        ·
          refine ⟨12372038439699536007288785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8248025626466357338192523 12372038439699536007288785)
          ·
            refine ⟨9279028829774652005466589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12372038439699536007288785 9279028829774652005466589)
            ·
              refine ⟨3479635811165494502049971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9279028829774652005466589 3479635811165494502049971)
              ·
                refine ⟨5219453716748241753074957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3479635811165494502049971 5219453716748241753074957)
                ·
                  refine ⟨1957295143780590657403109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5219453716748241753074957 1957295143780590657403109)
                  ·
                    refine ⟨366992839458860748263083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957295143780590657403109 366992839458860748263083)
                    ·
                      rfl

theorem cell23_2144148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2144148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144148 prefixEnd_2144148 := by exact prefixLift 2144148
  have htrace : WordTrace (prefixWord ++ tailWord_2144148) baseStart_2144148 baseEnd_2144148 := by
    simpa [prefixWord, tailWord_2144148, baseEnd_2144148] using wordTrace_append hprefix tailTrace_2144148
  have hstable : (prefixWord ++ tailWord_2144148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144148).length < 2 ^ (prefixWord ++ tailWord_2144148).sum := by decide
  have hdescent : baseEnd_2144148 < baseStart_2144148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144224 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_2144224 : Nat := 118140960795 + 2144224 * 2 ^ 59
def prefixEnd_2144224 : Nat := 4983230072969 + 3 ^ 40 * 2144224 * 2
def baseEnd_2144224 : Nat := 1101017542906323947438899

theorem tailTrace_2144224 : CollatzResearch.WordTrace tailWord_2144224 prefixEnd_2144224 1101017542906323947438899 := by
  unfold tailWord_2144224
  simp only [CollatzResearch.WordTrace]
  refine ⟨39103137091925063574647863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52137516122566751432863817 39103137091925063574647863)
  ·
    refine ⟨58654705637887595361971795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39103137091925063574647863 58654705637887595361971795)
    ·
      refine ⟨87982058456831393042957693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58654705637887595361971795 87982058456831393042957693)
      ·
        refine ⟨32993271921311772391109135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87982058456831393042957693 32993271921311772391109135)
        ·
          refine ⟨49489907881967658586663703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32993271921311772391109135 49489907881967658586663703)
          ·
            refine ⟨74234861822951487879995555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49489907881967658586663703 74234861822951487879995555)
            ·
              refine ⟨111352292734427231819993333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74234861822951487879995555 111352292734427231819993333)
              ·
                refine ⟨10439277443852552983124375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111352292734427231819993333 10439277443852552983124375)
                ·
                  refine ⟨15658916165778829474686563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10439277443852552983124375 15658916165778829474686563)
                  ·
                    refine ⟨23488374248668244212029845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15658916165778829474686563 23488374248668244212029845)
                    ·
                      refine ⟨1101017542906323947438899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23488374248668244212029845 1101017542906323947438899)
                      ·
                        rfl

theorem cell23_2144224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_2144224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144224 prefixEnd_2144224 := by exact prefixLift 2144224
  have htrace : WordTrace (prefixWord ++ tailWord_2144224) baseStart_2144224 baseEnd_2144224 := by
    simpa [prefixWord, tailWord_2144224, baseEnd_2144224] using wordTrace_append hprefix tailTrace_2144224
  have hstable : (prefixWord ++ tailWord_2144224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144224).length < 2 ^ (prefixWord ++ tailWord_2144224).sum := by decide
  have hdescent : baseEnd_2144224 < baseStart_2144224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144305 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 1, 3, 2]
def baseStart_2144305 : Nat := 118140960795 + 2144305 * 2 ^ 59
def prefixEnd_2144305 : Nat := 4983230072969 + 3 ^ 40 * 2144305 * 2
def baseEnd_2144305 : Nat := 1101059134839338130526027

theorem tailTrace_2144305 : CollatzResearch.WordTrace tailWord_2144305 prefixEnd_2144305 1101059134839338130526027 := by
  unfold tailWord_2144305
  simp only [CollatzResearch.WordTrace]
  refine ⟨78209228496556677982994369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52139485664371118655329579 78209228496556677982994369)
  ·
    refine ⟨58656921372417508487245777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78209228496556677982994369 58656921372417508487245777)
    ·
      refine ⟨43992691029313131365434333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58656921372417508487245777 43992691029313131365434333)
      ·
        refine ⟨16497259135992424262037875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43992691029313131365434333 16497259135992424262037875)
        ·
          refine ⟨24745888703988636393056813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16497259135992424262037875 24745888703988636393056813)
          ·
            refine ⟨9279708263995738647396305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24745888703988636393056813 9279708263995738647396305)
            ·
              refine ⟨6959781197996803985547229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9279708263995738647396305 6959781197996803985547229)
              ·
                refine ⟨2609917949248801494580211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6959781197996803985547229 2609917949248801494580211)
                ·
                  refine ⟨3914876923873202241870317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2609917949248801494580211 3914876923873202241870317)
                  ·
                    refine ⟨1468078846452450840701369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3914876923873202241870317 1468078846452450840701369)
                    ·
                      refine ⟨1101059134839338130526027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468078846452450840701369 1101059134839338130526027)
                      ·
                        rfl

theorem cell23_2144305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_2144305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144305 prefixEnd_2144305 := by exact prefixLift 2144305
  have htrace : WordTrace (prefixWord ++ tailWord_2144305) baseStart_2144305 baseEnd_2144305 := by
    simpa [prefixWord, tailWord_2144305, baseEnd_2144305] using wordTrace_append hprefix tailTrace_2144305
  have hstable : (prefixWord ++ tailWord_2144305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144305).length < 2 ^ (prefixWord ++ tailWord_2144305).sum := by decide
  have hdescent : baseEnd_2144305 < baseStart_2144305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144335 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 2, 2, 2]
def baseStart_2144335 : Nat := 118140960795 + 2144335 * 2 ^ 59
def prefixEnd_2144335 : Nat := 4983230072969 + 3 ^ 40 * 2144335 * 2
def baseEnd_2144335 : Nat := 1101074539258973013150889

theorem tailTrace_2144335 : CollatzResearch.WordTrace tailWord_2144335 prefixEnd_2144335 1101074539258973013150889 := by
  unfold tailWord_2144335
  simp only [CollatzResearch.WordTrace]
  refine ⟨78210322686447993106586459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52140215124298662071057639 78210322686447993106586459)
  ·
    refine ⟨117315484029671989659879689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78210322686447993106586459 117315484029671989659879689)
    ·
      refine ⟨87986613022253992244909767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117315484029671989659879689 87986613022253992244909767)
      ·
        refine ⟨131979919533380988367364651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87986613022253992244909767 131979919533380988367364651)
        ·
          refine ⟨197969879300071482551046977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131979919533380988367364651 197969879300071482551046977)
          ·
            refine ⟨148477409475053611913285233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197969879300071482551046977 148477409475053611913285233)
            ·
              refine ⟨111358057106290208934963925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148477409475053611913285233 111358057106290208934963925)
              ·
                refine ⟨2609954463428676771913217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111358057106290208934963925 2609954463428676771913217)
                ·
                  refine ⟨1957465847571507578934913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2609954463428676771913217 1957465847571507578934913)
                  ·
                    refine ⟨1468099385678630684201185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1957465847571507578934913 1468099385678630684201185)
                    ·
                      refine ⟨1101074539258973013150889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468099385678630684201185 1101074539258973013150889)
                      ·
                        rfl

theorem cell23_2144335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 2, 2].length) (baseStart_2144335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144335 prefixEnd_2144335 := by exact prefixLift 2144335
  have htrace : WordTrace (prefixWord ++ tailWord_2144335) baseStart_2144335 baseEnd_2144335 := by
    simpa [prefixWord, tailWord_2144335, baseEnd_2144335] using wordTrace_append hprefix tailTrace_2144335
  have hstable : (prefixWord ++ tailWord_2144335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144335).length < 2 ^ (prefixWord ++ tailWord_2144335).sum := by decide
  have hdescent : baseEnd_2144335 < baseStart_2144335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144351 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 3]
def baseStart_2144351 : Nat := 118140960795 + 2144351 * 2 ^ 59
def prefixEnd_2144351 : Nat := 4983230072969 + 3 ^ 40 * 2144351 * 2
def baseEnd_2144351 : Nat := 1101082754949444950550815

theorem tailTrace_2144351 : CollatzResearch.WordTrace tailWord_2144351 prefixEnd_2144351 1101082754949444950550815 := by
  unfold tailWord_2144351
  simp only [CollatzResearch.WordTrace]
  refine ⟨78210906254390027839168907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52140604169593351892779271 78210906254390027839168907)
  ·
    refine ⟨117316359381585041758753361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78210906254390027839168907 117316359381585041758753361)
    ·
      refine ⟨87987269536188781319065021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117316359381585041758753361 87987269536188781319065021)
      ·
        refine ⟨32995226076070792994649383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87987269536188781319065021 32995226076070792994649383)
        ·
          refine ⟨49492839114106189491974075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32995226076070792994649383 49492839114106189491974075)
          ·
            refine ⟨74239258671159284237961113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49492839114106189491974075 74239258671159284237961113)
            ·
              refine ⟨55679444003369463178470835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74239258671159284237961113 55679444003369463178470835)
              ·
                refine ⟨83519166005054194767706253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55679444003369463178470835 83519166005054194767706253)
                ·
                  refine ⟨31319687251895323037889845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83519166005054194767706253 31319687251895323037889845)
                  ·
                    refine ⟨2936220679865186534802173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31319687251895323037889845 2936220679865186534802173)
                    ·
                      refine ⟨1101082754949444950550815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936220679865186534802173 1101082754949444950550815)
                      ·
                        rfl

theorem cell23_2144351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_2144351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144351 prefixEnd_2144351 := by exact prefixLift 2144351
  have htrace : WordTrace (prefixWord ++ tailWord_2144351) baseStart_2144351 baseEnd_2144351 := by
    simpa [prefixWord, tailWord_2144351, baseEnd_2144351] using wordTrace_append hprefix tailTrace_2144351
  have hstable : (prefixWord ++ tailWord_2144351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144351).length < 2 ^ (prefixWord ++ tailWord_2144351).sum := by decide
  have hdescent : baseEnd_2144351 < baseStart_2144351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144375 : List Nat := [1, 1, 3, 1, 1, 5, 4, 2, 5]
def baseStart_2144375 : Nat := 118140960795 + 2144375 * 2 ^ 59
def prefixEnd_2144375 : Nat := 4983230072969 + 3 ^ 40 * 2144375 * 2
def baseEnd_2144375 : Nat := 122343897609461428516745

theorem tailTrace_2144375 : CollatzResearch.WordTrace tailWord_2144375 prefixEnd_2144375 122343897609461428516745 := by
  unfold tailWord_2144375
  simp only [CollatzResearch.WordTrace]
  refine ⟨78211781606303079938042579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52141187737535386625361719 78211781606303079938042579)
  ·
    refine ⟨117317672409454619907063869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78211781606303079938042579 117317672409454619907063869)
    ·
      refine ⟨43994127153545482465148951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117317672409454619907063869 43994127153545482465148951)
      ·
        refine ⟨65991190730318223697723427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43994127153545482465148951 65991190730318223697723427)
        ·
          refine ⟨98986786095477335546585141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65991190730318223697723427 98986786095477335546585141)
          ·
            refine ⟨9280011196451000207492357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98986786095477335546585141 9280011196451000207492357)
            ·
              refine ⟨1740002099334562538904817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9280011196451000207492357 1740002099334562538904817)
              ·
                refine ⟨1305001574500921904178613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740002099334562538904817 1305001574500921904178613)
                ·
                  refine ⟨122343897609461428516745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1305001574500921904178613 122343897609461428516745)
                  ·
                    rfl

theorem cell23_2144375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 5].length) (baseStart_2144375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144375 prefixEnd_2144375 := by exact prefixLift 2144375
  have htrace : WordTrace (prefixWord ++ tailWord_2144375) baseStart_2144375 baseEnd_2144375 := by
    simpa [prefixWord, tailWord_2144375, baseEnd_2144375] using wordTrace_append hprefix tailTrace_2144375
  have hstable : (prefixWord ++ tailWord_2144375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144375).length < 2 ^ (prefixWord ++ tailWord_2144375).sum := by decide
  have hdescent : baseEnd_2144375 < baseStart_2144375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144385 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2144385 : Nat := 118140960795 + 2144385 * 2 ^ 59
def prefixEnd_2144385 : Nat := 4983230072969 + 3 ^ 40 * 2144385 * 2
def baseEnd_2144385 : Nat := 1101100213291697817525659

theorem tailTrace_2144385 : CollatzResearch.WordTrace tailWord_2144385 prefixEnd_2144385 1101100213291697817525659 := by
  unfold tailWord_2144385
  simp only [CollatzResearch.WordTrace]
  refine ⟨78212146336266851645906609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52141430890844567763937739 78212146336266851645906609)
  ·
    refine ⟨58659109752200138734429957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78212146336266851645906609 58659109752200138734429957)
    ·
      refine ⟨10998583078537526012705617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58659109752200138734429957 10998583078537526012705617)
      ·
        refine ⟨8248937308903144509529213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10998583078537526012705617 8248937308903144509529213)
        ·
          refine ⟨3093351490838679191073455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8248937308903144509529213 3093351490838679191073455)
          ·
            refine ⟨4640027236258018786610183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093351490838679191073455 4640027236258018786610183)
            ·
              refine ⟨6960040854387028179915275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640027236258018786610183 6960040854387028179915275)
              ·
                refine ⟨10440061281580542269872913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960040854387028179915275 10440061281580542269872913)
                ·
                  refine ⟨7830045961185406702404685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10440061281580542269872913 7830045961185406702404685)
                  ·
                    refine ⟨2936267235444527513401757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7830045961185406702404685 2936267235444527513401757)
                    ·
                      refine ⟨1101100213291697817525659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936267235444527513401757 1101100213291697817525659)
                      ·
                        rfl

theorem cell23_2144385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2144385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144385 prefixEnd_2144385 := by exact prefixLift 2144385
  have htrace : WordTrace (prefixWord ++ tailWord_2144385) baseStart_2144385 baseEnd_2144385 := by
    simpa [prefixWord, tailWord_2144385, baseEnd_2144385] using wordTrace_append hprefix tailTrace_2144385
  have hstable : (prefixWord ++ tailWord_2144385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144385).length < 2 ^ (prefixWord ++ tailWord_2144385).sum := by decide
  have hdescent : baseEnd_2144385 < baseStart_2144385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144421 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_2144421 : Nat := 118140960795 + 2144421 * 2 ^ 59
def prefixEnd_2144421 : Nat := 4983230072969 + 3 ^ 40 * 2144421 * 2
def baseEnd_2144421 : Nat := 1101118698595259676675493

theorem tailTrace_2144421 : CollatzResearch.WordTrace tailWord_2144421 prefixEnd_2144421 1101118698595259676675493 := by
  unfold tailWord_2144421
  simp only [CollatzResearch.WordTrace]
  refine ⟨78213459364136429794217117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52142306242757619862811411 78213459364136429794217117)
  ·
    refine ⟨29330047261551161172831419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78213459364136429794217117 29330047261551161172831419)
    ·
      refine ⟨43995070892326741759247129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29330047261551161172831419 43995070892326741759247129)
      ·
        refine ⟨32996303169245056319435347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43995070892326741759247129 32996303169245056319435347)
        ·
          refine ⟨49494454753867584479153021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32996303169245056319435347 49494454753867584479153021)
          ·
            refine ⟨18560420532700344179682383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49494454753867584479153021 18560420532700344179682383)
            ·
              refine ⟨27840630799050516269523575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18560420532700344179682383 27840630799050516269523575)
              ·
                refine ⟨41760946198575774404285363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27840630799050516269523575 41760946198575774404285363)
                ·
                  refine ⟨62641419297863661606428045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41760946198575774404285363 62641419297863661606428045)
                  ·
                    refine ⟨23490532236698873102410517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62641419297863661606428045 23490532236698873102410517)
                    ·
                      refine ⟨1101118698595259676675493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23490532236698873102410517 1101118698595259676675493)
                      ·
                        rfl

theorem cell23_2144421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_2144421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144421 prefixEnd_2144421 := by exact prefixLift 2144421
  have htrace : WordTrace (prefixWord ++ tailWord_2144421) baseStart_2144421 baseEnd_2144421 := by
    simpa [prefixWord, tailWord_2144421, baseEnd_2144421] using wordTrace_append hprefix tailTrace_2144421
  have hstable : (prefixWord ++ tailWord_2144421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144421).length < 2 ^ (prefixWord ++ tailWord_2144421).sum := by decide
  have hdescent : baseEnd_2144421 < baseStart_2144421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144458 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_2144458 : Nat := 118140960795 + 2144458 * 2 ^ 59
def prefixEnd_2144458 : Nat := 4983230072969 + 3 ^ 40 * 2144458 * 2
def baseEnd_2144458 : Nat := 1101137697379476031912823

theorem tailTrace_2144458 : CollatzResearch.WordTrace tailWord_2144458 prefixEnd_2144458 1101137697379476031912823 := by
  unfold tailWord_2144458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19553702216250596278328507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52143205910001590075542685 19553702216250596278328507)
  ·
    refine ⟨29330553324375894417492761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19553702216250596278328507 29330553324375894417492761)
    ·
      refine ⟨21997914993281920813119571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29330553324375894417492761 21997914993281920813119571)
      ·
        refine ⟨32996872489922881219679357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21997914993281920813119571 32996872489922881219679357)
        ·
          refine ⟨12373827183721080457379759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32996872489922881219679357 12373827183721080457379759)
          ·
            refine ⟨18560740775581620686069639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12373827183721080457379759 18560740775581620686069639)
            ·
              refine ⟨27841111163372431029104459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18560740775581620686069639 27841111163372431029104459)
              ·
                refine ⟨41761666745058646543656689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27841111163372431029104459 41761666745058646543656689)
                ·
                  refine ⟨31321250058793984907742517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41761666745058646543656689 31321250058793984907742517)
                  ·
                    refine ⟨2936367193011936085100861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31321250058793984907742517 2936367193011936085100861)
                    ·
                      refine ⟨1101137697379476031912823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936367193011936085100861 1101137697379476031912823)
                      ·
                        rfl

theorem cell23_2144458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_2144458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144458 prefixEnd_2144458 := by exact prefixLift 2144458
  have htrace : WordTrace (prefixWord ++ tailWord_2144458) baseStart_2144458 baseEnd_2144458 := by
    simpa [prefixWord, tailWord_2144458, baseEnd_2144458] using wordTrace_append hprefix tailTrace_2144458
  have hstable : (prefixWord ++ tailWord_2144458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144458).length < 2 ^ (prefixWord ++ tailWord_2144458).sum := by decide
  have hdescent : baseEnd_2144458 < baseStart_2144458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144535 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2144535 : Nat := 118140960795 + 2144535 * 2 ^ 59
def prefixEnd_2144535 : Nat := 4983230072969 + 3 ^ 40 * 2144535 * 2
def baseEnd_2144535 : Nat := 1101177235389872230649969

theorem tailTrace_2144535 : CollatzResearch.WordTrace tailWord_2144535 prefixEnd_2144535 1101177235389872230649969 := by
  unfold tailWord_2144535
  simp only [CollatzResearch.WordTrace]
  refine ⟨78217617285723427263867059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52145078190482284842578039 78217617285723427263867059)
  ·
    refine ⟨117326425928585140895800589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78217617285723427263867059 117326425928585140895800589)
    ·
      refine ⟨43997409723219427835925221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117326425928585140895800589 43997409723219427835925221)
      ·
        refine ⟨8249514323103642719235979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43997409723219427835925221 8249514323103642719235979)
        ·
          refine ⟨12374271484655464078853969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8249514323103642719235979 12374271484655464078853969)
          ·
            refine ⟨9280703613491598059140477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12374271484655464078853969 9280703613491598059140477)
            ·
              refine ⟨3480263855059349272177679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9280703613491598059140477 3480263855059349272177679)
              ·
                refine ⟨5220395782589023908266519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480263855059349272177679 5220395782589023908266519)
                ·
                  refine ⟨7830593673883535862399779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220395782589023908266519 7830593673883535862399779)
                  ·
                    refine ⟨11745890510825303793599669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7830593673883535862399779 11745890510825303793599669)
                    ·
                      refine ⟨1101177235389872230649969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11745890510825303793599669 1101177235389872230649969)
                      ·
                        rfl

theorem cell23_2144535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2144535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144535 prefixEnd_2144535 := by exact prefixLift 2144535
  have htrace : WordTrace (prefixWord ++ tailWord_2144535) baseStart_2144535 baseEnd_2144535 := by
    simpa [prefixWord, tailWord_2144535, baseEnd_2144535] using wordTrace_append hprefix tailTrace_2144535
  have hstable : (prefixWord ++ tailWord_2144535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144535).length < 2 ^ (prefixWord ++ tailWord_2144535).sum := by decide
  have hdescent : baseEnd_2144535 < baseStart_2144535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144538 : List Nat := [3, 1, 1, 3, 4, 11]
def baseStart_2144538 : Nat := 118140960795 + 2144538 * 2 ^ 59
def prefixEnd_2144538 : Nat := 4983230072969 + 3 ^ 40 * 2144538 * 2
def baseEnd_2144538 : Nat := 4531599900542533822685

theorem tailTrace_2144538 : CollatzResearch.WordTrace tailWord_2144538 prefixEnd_2144538 4531599900542533822685 := by
  unfold tailWord_2144538
  simp only [CollatzResearch.WordTrace]
  refine ⟨19554431676178139694056567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52145151136475039184150845 19554431676178139694056567)
  ·
    refine ⟨29331647514267209541084851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19554431676178139694056567 29331647514267209541084851)
    ·
      refine ⟨43997471271400814311627277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29331647514267209541084851 43997471271400814311627277)
      ·
        refine ⟨16499051726775305366860229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43997471271400814311627277 16499051726775305366860229)
        ·
          refine ⟨3093572198770369756286293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16499051726775305366860229 3093572198770369756286293)
          ·
            refine ⟨4531599900542533822685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3093572198770369756286293 4531599900542533822685)
            ·
              rfl

theorem cell23_2144538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 11].length) (baseStart_2144538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144538 prefixEnd_2144538 := by exact prefixLift 2144538
  have htrace : WordTrace (prefixWord ++ tailWord_2144538) baseStart_2144538 baseEnd_2144538 := by
    simpa [prefixWord, tailWord_2144538, baseEnd_2144538] using wordTrace_append hprefix tailTrace_2144538
  have hstable : (prefixWord ++ tailWord_2144538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144538).length < 2 ^ (prefixWord ++ tailWord_2144538).sum := by decide
  have hdescent : baseEnd_2144538 < baseStart_2144538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144562 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2144562 : Nat := 118140960795 + 2144562 * 2 ^ 59
def prefixEnd_2144562 : Nat := 4983230072969 + 3 ^ 40 * 2144562 * 2
def baseEnd_2144562 : Nat := 1101191099367543625012345

theorem tailTrace_2144562 : CollatzResearch.WordTrace tailWord_2144562 prefixEnd_2144562 1101191099367543625012345 := by
  unfold tailWord_2144562
  simp only [CollatzResearch.WordTrace]
  refine ⟨19554650514156402718774985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52145734704417073916733293 19554650514156402718774985)
  ·
    refine ⟨14665987885617302039081239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19554650514156402718774985 14665987885617302039081239)
    ·
      refine ⟨21998981828425953058621859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14665987885617302039081239 21998981828425953058621859)
      ·
        refine ⟨32998472742638929587932789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21998981828425953058621859 32998472742638929587932789)
        ·
          refine ⟨3093606819622399648868699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32998472742638929587932789 3093606819622399648868699)
          ·
            refine ⟨4640410229433599473303049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093606819622399648868699 4640410229433599473303049)
            ·
              refine ⟨3480307672075199604977287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4640410229433599473303049 3480307672075199604977287)
              ·
                refine ⟨5220461508112799407465931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480307672075199604977287 5220461508112799407465931)
                ·
                  refine ⟨7830692262169199111198897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5220461508112799407465931 7830692262169199111198897)
                  ·
                    refine ⟨5873019196626899333399173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7830692262169199111198897 5873019196626899333399173)
                    ·
                      refine ⟨1101191099367543625012345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5873019196626899333399173 1101191099367543625012345)
                      ·
                        rfl

theorem cell23_2144562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2144562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144562 prefixEnd_2144562 := by exact prefixLift 2144562
  have htrace : WordTrace (prefixWord ++ tailWord_2144562) baseStart_2144562 baseEnd_2144562 := by
    simpa [prefixWord, tailWord_2144562, baseEnd_2144562] using wordTrace_append hprefix tailTrace_2144562
  have hstable : (prefixWord ++ tailWord_2144562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144562).length < 2 ^ (prefixWord ++ tailWord_2144562).sum := by decide
  have hdescent : baseEnd_2144562 < baseStart_2144562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144615 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 2, 6]
def baseStart_2144615 : Nat := 118140960795 + 2144615 * 2 ^ 59
def prefixEnd_2144615 : Nat := 4983230072969 + 3 ^ 40 * 2144615 * 2
def baseEnd_2144615 : Nat := 367072771280743972549867

theorem tailTrace_2144615 : CollatzResearch.WordTrace tailWord_2144615 prefixEnd_2144615 367072771280743972549867 := by
  unfold tailWord_2144615
  simp only [CollatzResearch.WordTrace]
  refine ⟨78220535125433600926779299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52147023416955733951186199 78220535125433600926779299)
  ·
    refine ⟨117330802688150401390168949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78220535125433600926779299 117330802688150401390168949)
    ·
      refine ⟨10999762752014100130328339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117330802688150401390168949 10999762752014100130328339)
      ·
        refine ⟨16499644128021150195492509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10999762752014100130328339 16499644128021150195492509)
        ·
          refine ⟨6187366548007931323309691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16499644128021150195492509 6187366548007931323309691)
          ·
            refine ⟨9281049822011896984964537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6187366548007931323309691 9281049822011896984964537)
            ·
              refine ⟨6960787366508922738723403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9281049822011896984964537 6960787366508922738723403)
              ·
                refine ⟨10441181049763384108085105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960787366508922738723403 10441181049763384108085105)
                ·
                  refine ⟨7830885787322538081063829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10441181049763384108085105 7830885787322538081063829)
                  ·
                    refine ⟨367072771280743972549867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7830885787322538081063829 367072771280743972549867)
                    ·
                      rfl

theorem cell23_2144615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_2144615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144615 prefixEnd_2144615 := by exact prefixLift 2144615
  have htrace : WordTrace (prefixWord ++ tailWord_2144615) baseStart_2144615 baseEnd_2144615 := by
    simpa [prefixWord, tailWord_2144615, baseEnd_2144615] using wordTrace_append hprefix tailTrace_2144615
  have hstable : (prefixWord ++ tailWord_2144615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144615).length < 2 ^ (prefixWord ++ tailWord_2144615).sum := by decide
  have hdescent : baseEnd_2144615 < baseStart_2144615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144616 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2144616 : Nat := 118140960795 + 2144616 * 2 ^ 59
def prefixEnd_2144616 : Nat := 4983230072969 + 3 ^ 40 * 2144616 * 2
def baseEnd_2144616 : Nat := 1101218827322886413737097

theorem tailTrace_2144616 : CollatzResearch.WordTrace tailWord_2144616 prefixEnd_2144616 1101218827322886413737097 := by
  unfold tailWord_2144616
  simp only [CollatzResearch.WordTrace]
  refine ⟨39110285799214989048782851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52147047732286652065043801 39110285799214989048782851)
  ·
    refine ⟨58665428698822483573174277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39110285799214989048782851 58665428698822483573174277)
    ·
      refine ⟨10999767881029215669970177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58665428698822483573174277 10999767881029215669970177)
      ·
        refine ⟨8249825910771911752477633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10999767881029215669970177 8249825910771911752477633)
        ·
          refine ⟨6187369433078933814358225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8249825910771911752477633 6187369433078933814358225)
          ·
            refine ⟨4640527074809200360768669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6187369433078933814358225 4640527074809200360768669)
            ·
              refine ⟨1740197653053450135288251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4640527074809200360768669 1740197653053450135288251)
              ·
                refine ⟨2610296479580175202932377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740197653053450135288251 2610296479580175202932377)
                ·
                  refine ⟨1957722359685131402199283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2610296479580175202932377 1957722359685131402199283)
                  ·
                    refine ⟨2936583539527697103298925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1957722359685131402199283 2936583539527697103298925)
                    ·
                      refine ⟨1101218827322886413737097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936583539527697103298925 1101218827322886413737097)
                      ·
                        rfl

theorem cell23_2144616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2144616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144616 prefixEnd_2144616 := by exact prefixLift 2144616
  have htrace : WordTrace (prefixWord ++ tailWord_2144616) baseStart_2144616 baseEnd_2144616 := by
    simpa [prefixWord, tailWord_2144616, baseEnd_2144616] using wordTrace_append hprefix tailTrace_2144616
  have hstable : (prefixWord ++ tailWord_2144616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144616).length < 2 ^ (prefixWord ++ tailWord_2144616).sum := by decide
  have hdescent : baseEnd_2144616 < baseStart_2144616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144673 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2144673 : Nat := 118140960795 + 2144673 * 2 ^ 59
def prefixEnd_2144673 : Nat := 4983230072969 + 3 ^ 40 * 2144673 * 2
def baseEnd_2144673 : Nat := 1101248095720192690724335

theorem tailTrace_2144673 : CollatzResearch.WordTrace tailWord_2144673 prefixEnd_2144673 1101248095720192690724335 := by
  unfold tailWord_2144673
  simp only [CollatzResearch.WordTrace]
  refine ⟨78222650559223476832390673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52148433706148984554927115 78222650559223476832390673)
  ·
    refine ⟨58666987919417607624293005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78222650559223476832390673 58666987919417607624293005)
    ·
      refine ⟨22000120469781602859109877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58666987919417607624293005 22000120469781602859109877)
      ·
        refine ⟨2062511294042025268041551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22000120469781602859109877 2062511294042025268041551)
        ·
          refine ⟨3093766941063037902062327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062511294042025268041551 3093766941063037902062327)
          ·
            refine ⟨4640650411594556853093491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093766941063037902062327 4640650411594556853093491)
            ·
              refine ⟨6960975617391835279640237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640650411594556853093491 6960975617391835279640237)
              ·
                refine ⟨2610365856521938229865089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6960975617391835279640237 2610365856521938229865089)
                ·
                  refine ⟨1957774392391453672398817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2610365856521938229865089 1957774392391453672398817)
                  ·
                    refine ⟨1468330794293590254299113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1957774392391453672398817 1468330794293590254299113)
                    ·
                      refine ⟨1101248095720192690724335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468330794293590254299113 1101248095720192690724335)
                      ·
                        rfl

theorem cell23_2144673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2144673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144673 prefixEnd_2144673 := by exact prefixLift 2144673
  have htrace : WordTrace (prefixWord ++ tailWord_2144673) baseStart_2144673 baseEnd_2144673 := by
    simpa [prefixWord, tailWord_2144673, baseEnd_2144673] using wordTrace_append hprefix tailTrace_2144673
  have hstable : (prefixWord ++ tailWord_2144673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144673).length < 2 ^ (prefixWord ++ tailWord_2144673).sum := by decide
  have hdescent : baseEnd_2144673 < baseStart_2144673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144712 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_2144712 : Nat := 118140960795 + 2144712 * 2 ^ 59
def prefixEnd_2144712 : Nat := 4983230072969 + 3 ^ 40 * 2144712 * 2
def baseEnd_2144712 : Nat := 1101268121465718038136655

theorem tailTrace_2144712 : CollatzResearch.WordTrace tailWord_2144712 prefixEnd_2144712 1101268121465718038136655 := by
  unfold tailWord_2144712
  simp only [CollatzResearch.WordTrace]
  refine ⟨39112036503041093246530195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52149382004054790995373593 39112036503041093246530195)
  ·
    refine ⟨58668054754561639869795293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39112036503041093246530195 58668054754561639869795293)
    ·
      refine ⟨22000520532960614951173235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58668054754561639869795293 22000520532960614951173235)
      ·
        refine ⟨33000780799440922426759853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22000520532960614951173235 33000780799440922426759853)
        ·
          refine ⟨12375292799790345910034945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33000780799440922426759853 12375292799790345910034945)
          ·
            refine ⟨9281469599842759432526209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12375292799790345910034945 9281469599842759432526209)
            ·
              refine ⟨6961102199882069574394657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9281469599842759432526209 6961102199882069574394657)
              ·
                refine ⟨5220826649911552180795993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6961102199882069574394657 5220826649911552180795993)
                ·
                  refine ⟨3915619987433664135596995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5220826649911552180795993 3915619987433664135596995)
                  ·
                    refine ⟨5873429981150496203395493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3915619987433664135596995 5873429981150496203395493)
                    ·
                      refine ⟨1101268121465718038136655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5873429981150496203395493 1101268121465718038136655)
                      ·
                        rfl

theorem cell23_2144712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_2144712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144712 prefixEnd_2144712 := by exact prefixLift 2144712
  have htrace : WordTrace (prefixWord ++ tailWord_2144712) baseStart_2144712 baseEnd_2144712 := by
    simpa [prefixWord, tailWord_2144712, baseEnd_2144712] using wordTrace_append hprefix tailTrace_2144712
  have hstable : (prefixWord ++ tailWord_2144712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144712).length < 2 ^ (prefixWord ++ tailWord_2144712).sum := by decide
  have hdescent : baseEnd_2144712 < baseStart_2144712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144715 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 3]
def baseStart_2144715 : Nat := 118140960795 + 2144715 * 2 ^ 59
def prefixEnd_2144715 : Nat := 4983230072969 + 3 ^ 40 * 2144715 * 2
def baseEnd_2144715 : Nat := 1101269661907681526399141

theorem tailTrace_2144715 : CollatzResearch.WordTrace tailWord_2144715 prefixEnd_2144715 1101269661907681526399141 := by
  unfold tailWord_2144715
  simp only [CollatzResearch.WordTrace]
  refine ⟨78224182425071318005419599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52149454950047545336946399 78224182425071318005419599)
  ·
    refine ⟨117336273637606977008129399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78224182425071318005419599 117336273637606977008129399)
    ·
      refine ⟨176004410456410465512194099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117336273637606977008129399 176004410456410465512194099)
      ·
        refine ⟨264006615684615698268291149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176004410456410465512194099 264006615684615698268291149)
        ·
          refine ⟨99002480881730886850609181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264006615684615698268291149 99002480881730886850609181)
          ·
            refine ⟨37125930330649082568978443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99002480881730886850609181 37125930330649082568978443)
            ·
              refine ⟨55688895495973623853467665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37125930330649082568978443 55688895495973623853467665)
              ·
                refine ⟨41766671621980217890100749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55688895495973623853467665 41766671621980217890100749)
                ·
                  refine ⟨15662501858242581708787781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41766671621980217890100749 15662501858242581708787781)
                  ·
                    refine ⟨2936719098420484070397709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15662501858242581708787781 2936719098420484070397709)
                    ·
                      refine ⟨1101269661907681526399141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936719098420484070397709 1101269661907681526399141)
                      ·
                        rfl

theorem cell23_2144715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 3].length) (baseStart_2144715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144715 prefixEnd_2144715 := by exact prefixLift 2144715
  have htrace : WordTrace (prefixWord ++ tailWord_2144715) baseStart_2144715 baseEnd_2144715 := by
    simpa [prefixWord, tailWord_2144715, baseEnd_2144715] using wordTrace_append hprefix tailTrace_2144715
  have hstable : (prefixWord ++ tailWord_2144715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144715).length < 2 ^ (prefixWord ++ tailWord_2144715).sum := by decide
  have hdescent : baseEnd_2144715 < baseStart_2144715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144739 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 3, 4]
def baseStart_2144739 : Nat := 118140960795 + 2144739 * 2 ^ 59
def prefixEnd_2144739 : Nat := 4983230072969 + 3 ^ 40 * 2144739 * 2
def baseEnd_2144739 : Nat := 367093995147796477499677

theorem tailTrace_2144739 : CollatzResearch.WordTrace tailWord_2144739 prefixEnd_2144739 367093995147796477499677 := by
  unfold tailWord_2144739
  simp only [CollatzResearch.WordTrace]
  refine ⟨78225057776984370104293271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52150038517989580069528847 78225057776984370104293271)
  ·
    refine ⟨117337586665476555156439907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78225057776984370104293271 117337586665476555156439907)
    ·
      refine ⟨176006379998214832734659861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117337586665476555156439907 176006379998214832734659861)
      ·
        refine ⟨8250299062416320284437181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 176006379998214832734659861 8250299062416320284437181)
        ·
          refine ⟨3093862148406120106663943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8250299062416320284437181 3093862148406120106663943)
          ·
            refine ⟨4640793222609180159995915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093862148406120106663943 4640793222609180159995915)
            ·
              refine ⟨6961189833913770239993873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640793222609180159995915 6961189833913770239993873)
              ·
                refine ⟨5220892375435327679995405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6961189833913770239993873 5220892375435327679995405)
                ·
                  refine ⟨1957834640788247879998277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5220892375435327679995405 1957834640788247879998277)
                  ·
                    refine ⟨367093995147796477499677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957834640788247879998277 367093995147796477499677)
                    ·
                      rfl

theorem cell23_2144739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 4].length) (baseStart_2144739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144739 prefixEnd_2144739 := by exact prefixLift 2144739
  have htrace : WordTrace (prefixWord ++ tailWord_2144739) baseStart_2144739 baseEnd_2144739 := by
    simpa [prefixWord, tailWord_2144739, baseEnd_2144739] using wordTrace_append hprefix tailTrace_2144739
  have hstable : (prefixWord ++ tailWord_2144739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144739).length < 2 ^ (prefixWord ++ tailWord_2144739).sum := by decide
  have hdescent : baseEnd_2144739 < baseStart_2144739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144745 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 3]
def baseStart_2144745 : Nat := 118140960795 + 2144745 * 2 ^ 59
def prefixEnd_2144745 : Nat := 4983230072969 + 3 ^ 40 * 2144745 * 2
def baseEnd_2144745 : Nat := 1101285066327316409024003

theorem tailTrace_2144745 : CollatzResearch.WordTrace tailWord_2144745 prefixEnd_2144745 1101285066327316409024003 := by
  unfold tailWord_2144745
  simp only [CollatzResearch.WordTrace]
  refine ⟨78225276614962633129011689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52150184409975088752674459 78225276614962633129011689)
  ·
    refine ⟨58668957461221974846758767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78225276614962633129011689 58668957461221974846758767)
    ·
      refine ⟨88003436191832962270138151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58668957461221974846758767 88003436191832962270138151)
      ·
        refine ⟨132005154287749443405207227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88003436191832962270138151 132005154287749443405207227)
        ·
          refine ⟨198007731431624165107810841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132005154287749443405207227 198007731431624165107810841)
          ·
            refine ⟨148505798573718123830858131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198007731431624165107810841 148505798573718123830858131)
            ·
              refine ⟨222758697860577185746287197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148505798573718123830858131 222758697860577185746287197)
              ·
                refine ⟨83534511697716444654857699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222758697860577185746287197 83534511697716444654857699)
                ·
                  refine ⟨125301767546574666982286549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83534511697716444654857699 125301767546574666982286549)
                  ·
                    refine ⟨2936760176872843757397341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 125301767546574666982286549 2936760176872843757397341)
                    ·
                      refine ⟨1101285066327316409024003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936760176872843757397341 1101285066327316409024003)
                      ·
                        rfl

theorem cell23_2144745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_2144745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144745 prefixEnd_2144745 := by exact prefixLift 2144745
  have htrace : WordTrace (prefixWord ++ tailWord_2144745) baseStart_2144745 baseEnd_2144745 := by
    simpa [prefixWord, tailWord_2144745, baseEnd_2144745] using wordTrace_append hprefix tailTrace_2144745
  have hstable : (prefixWord ++ tailWord_2144745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144745).length < 2 ^ (prefixWord ++ tailWord_2144745).sum := by decide
  have hdescent : baseEnd_2144745 < baseStart_2144745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144749 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2144749 : Nat := 118140960795 + 2144749 * 2 ^ 59
def prefixEnd_2144749 : Nat := 4983230072969 + 3 ^ 40 * 2144749 * 2
def baseEnd_2144749 : Nat := 1101287120249934393373985

theorem tailTrace_2144749 : CollatzResearch.WordTrace tailWord_2144749 prefixEnd_2144749 1101287120249934393373985 := by
  unfold tailWord_2144749
  simp only [CollatzResearch.WordTrace]
  refine ⟨78225422506948141812157301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52150281671298761208104867 78225422506948141812157301)
  ·
    refine ⟨7333633360026388294889747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78225422506948141812157301 7333633360026388294889747)
    ·
      refine ⟨11000450040039582442334621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7333633360026388294889747 11000450040039582442334621)
      ·
        refine ⟨4125168765014843415875483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11000450040039582442334621 4125168765014843415875483)
        ·
          refine ⟨6187753147522265123813225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4125168765014843415875483 6187753147522265123813225)
          ·
            refine ⟨4640814860641698842859919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6187753147522265123813225 4640814860641698842859919)
            ·
              refine ⟨6961222290962548264289879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640814860641698842859919 6961222290962548264289879)
              ·
                refine ⟨10441833436443822396434819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6961222290962548264289879 10441833436443822396434819)
                ·
                  refine ⟨15662750154665733594652229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10441833436443822396434819 15662750154665733594652229)
                  ·
                    refine ⟨2936765653999825048997293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15662750154665733594652229 2936765653999825048997293)
                    ·
                      refine ⟨1101287120249934393373985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936765653999825048997293 1101287120249934393373985)
                      ·
                        rfl

theorem cell23_2144749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2144749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144749 prefixEnd_2144749 := by exact prefixLift 2144749
  have htrace : WordTrace (prefixWord ++ tailWord_2144749) baseStart_2144749 baseEnd_2144749 := by
    simpa [prefixWord, tailWord_2144749, baseEnd_2144749] using wordTrace_append hprefix tailTrace_2144749
  have hstable : (prefixWord ++ tailWord_2144749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144749).length < 2 ^ (prefixWord ++ tailWord_2144749).sum := by decide
  have hdescent : baseEnd_2144749 < baseStart_2144749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144769 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 6]
def baseStart_2144769 : Nat := 118140960795 + 2144769 * 2 ^ 59
def prefixEnd_2144769 : Nat := 4983230072969 + 3 ^ 40 * 2144769 * 2
def baseEnd_2144769 : Nat := 122366376651447146124877

theorem tailTrace_2144769 : CollatzResearch.WordTrace tailWord_2144769 prefixEnd_2144769 122366376651447146124877 := by
  unfold tailWord_2144769
  simp only [CollatzResearch.WordTrace]
  refine ⟨78226151966875685227885361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52150767977917123485256907 78226151966875685227885361)
  ·
    refine ⟨58669613975156763920914021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78226151966875685227885361 58669613975156763920914021)
    ·
      refine ⟨11000552620341893235171379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58669613975156763920914021 11000552620341893235171379)
      ·
        refine ⟨16500828930512839852757069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11000552620341893235171379 16500828930512839852757069)
        ·
          refine ⟨6187810848942314944783901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16500828930512839852757069 6187810848942314944783901)
          ·
            refine ⟨2320429068353368104293963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6187810848942314944783901 2320429068353368104293963)
            ·
              refine ⟨3480643602530052156440945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320429068353368104293963 3480643602530052156440945)
              ·
                refine ⟨2610482701897539117330709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3480643602530052156440945 2610482701897539117330709)
                ·
                  refine ⟨122366376651447146124877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2610482701897539117330709 122366376651447146124877)
                  ·
                    rfl

theorem cell23_2144769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 6].length) (baseStart_2144769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144769 prefixEnd_2144769 := by exact prefixLift 2144769
  have htrace : WordTrace (prefixWord ++ tailWord_2144769) baseStart_2144769 baseEnd_2144769 := by
    simpa [prefixWord, tailWord_2144769, baseEnd_2144769] using wordTrace_append hprefix tailTrace_2144769
  have hstable : (prefixWord ++ tailWord_2144769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144769).length < 2 ^ (prefixWord ++ tailWord_2144769).sum := by decide
  have hdescent : baseEnd_2144769 < baseStart_2144769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144772 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2144772 : Nat := 118140960795 + 2144772 * 2 ^ 59
def prefixEnd_2144772 : Nat := 4983230072969 + 3 ^ 40 * 2144772 * 2
def baseEnd_2144772 : Nat := 1101298930304987803386379

theorem tailTrace_2144772 : CollatzResearch.WordTrace tailWord_2144772 prefixEnd_2144772 1101298930304987803386379 := by
  unfold tailWord_2144772
  simp only [CollatzResearch.WordTrace]
  refine ⟨39113130692932408370122285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52150840923909877826829713 39113130692932408370122285)
  ·
    refine ⟨14667424009849653138795857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39113130692932408370122285 14667424009849653138795857)
    ·
      refine ⟨11000568007387239854096893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14667424009849653138795857 11000568007387239854096893)
      ·
        refine ⟨4125213002770214945286335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11000568007387239854096893 4125213002770214945286335)
        ·
          refine ⟨6187819504155322417929503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4125213002770214945286335 6187819504155322417929503)
          ·
            refine ⟨9281729256232983626894255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6187819504155322417929503 9281729256232983626894255)
            ·
              refine ⟨13922593884349475440341383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9281729256232983626894255 13922593884349475440341383)
              ·
                refine ⟨20883890826524213160512075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13922593884349475440341383 20883890826524213160512075)
                ·
                  refine ⟨31325836239786319740768113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20883890826524213160512075 31325836239786319740768113)
                  ·
                    refine ⟨23494377179839739805576085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31325836239786319740768113 23494377179839739805576085)
                    ·
                      refine ⟨1101298930304987803386379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23494377179839739805576085 1101298930304987803386379)
                      ·
                        rfl

theorem cell23_2144772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2144772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144772 prefixEnd_2144772 := by exact prefixLift 2144772
  have htrace : WordTrace (prefixWord ++ tailWord_2144772) baseStart_2144772 baseEnd_2144772 := by
    simpa [prefixWord, tailWord_2144772, baseEnd_2144772] using wordTrace_append hprefix tailTrace_2144772
  have hstable : (prefixWord ++ tailWord_2144772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144772).length < 2 ^ (prefixWord ++ tailWord_2144772).sum := by decide
  have hdescent : baseEnd_2144772 < baseStart_2144772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144779 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 3]
def baseStart_2144779 : Nat := 118140960795 + 2144779 * 2 ^ 59
def prefixEnd_2144779 : Nat := 4983230072969 + 3 ^ 40 * 2144779 * 2
def baseEnd_2144779 : Nat := 1101302524669569275998847

theorem tailTrace_2144779 : CollatzResearch.WordTrace tailWord_2144779 prefixEnd_2144779 1101302524669569275998847 := by
  unfold tailWord_2144779
  simp only [CollatzResearch.WordTrace]
  refine ⟨78226516696839456935749391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52151011131226304623832927 78226516696839456935749391)
  ·
    refine ⟨117339775045259185403624087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78226516696839456935749391 117339775045259185403624087)
    ·
      refine ⟨176009662567888778105436131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117339775045259185403624087 176009662567888778105436131)
      ·
        refine ⟨264014493851833167158154197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176009662567888778105436131 264014493851833167158154197)
        ·
          refine ⟨6187839699652339855269239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 264014493851833167158154197 6187839699652339855269239)
          ·
            refine ⟨9281759549478509782903859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6187839699652339855269239 9281759549478509782903859)
            ·
              refine ⟨13922639324217764674355789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9281759549478509782903859 13922639324217764674355789)
              ·
                refine ⟨5220989746581661752883421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13922639324217764674355789 5220989746581661752883421)
                ·
                  refine ⟨1957871154968123157331283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5220989746581661752883421 1957871154968123157331283)
                  ·
                    refine ⟨2936806732452184735996925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1957871154968123157331283 2936806732452184735996925)
                    ·
                      refine ⟨1101302524669569275998847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936806732452184735996925 1101302524669569275998847)
                      ·
                        rfl

theorem cell23_2144779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 3].length) (baseStart_2144779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144779 prefixEnd_2144779 := by exact prefixLift 2144779
  have htrace : WordTrace (prefixWord ++ tailWord_2144779) baseStart_2144779 baseEnd_2144779 := by
    simpa [prefixWord, tailWord_2144779, baseEnd_2144779] using wordTrace_append hprefix tailTrace_2144779
  have hstable : (prefixWord ++ tailWord_2144779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144779).length < 2 ^ (prefixWord ++ tailWord_2144779).sum := by decide
  have hdescent : baseEnd_2144779 < baseStart_2144779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144785 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_2144785 : Nat := 118140960795 + 2144785 * 2 ^ 59
def prefixEnd_2144785 : Nat := 4983230072969 + 3 ^ 40 * 2144785 * 2
def baseEnd_2144785 : Nat := 1101305605553496252523819

theorem tailTrace_2144785 : CollatzResearch.WordTrace tailWord_2144785 prefixEnd_2144785 1101305605553496252523819 := by
  unfold tailWord_2144785
  simp only [CollatzResearch.WordTrace]
  refine ⟨78226735534817719960467809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52151157023211813306978539 78226735534817719960467809)
  ·
    refine ⟨58670051651113289970350857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78226735534817719960467809 58670051651113289970350857)
    ·
      refine ⟨44002538738334967477763143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58670051651113289970350857 44002538738334967477763143)
      ·
        refine ⟨66003808107502451216644715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44002538738334967477763143 66003808107502451216644715)
        ·
          refine ⟨99005712161253676824967073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66003808107502451216644715 99005712161253676824967073)
          ·
            refine ⟨74254284120940257618725305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99005712161253676824967073 74254284120940257618725305)
            ·
              refine ⟨55690713090705193214043979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74254284120940257618725305 55690713090705193214043979)
              ·
                refine ⟨83536069636057789821065969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55690713090705193214043979 83536069636057789821065969)
                ·
                  refine ⟨62652052227043342365799477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83536069636057789821065969 62652052227043342365799477)
                  ·
                    refine ⟨5873629896285313346793701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62652052227043342365799477 5873629896285313346793701)
                    ·
                      refine ⟨1101305605553496252523819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5873629896285313346793701 1101305605553496252523819)
                      ·
                        rfl

theorem cell23_2144785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_2144785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144785 prefixEnd_2144785 := by exact prefixLift 2144785
  have htrace : WordTrace (prefixWord ++ tailWord_2144785) baseStart_2144785 baseEnd_2144785 := by
    simpa [prefixWord, tailWord_2144785, baseEnd_2144785] using wordTrace_append hprefix tailTrace_2144785
  have hstable : (prefixWord ++ tailWord_2144785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144785).length < 2 ^ (prefixWord ++ tailWord_2144785).sum := by decide
  have hdescent : baseEnd_2144785 < baseStart_2144785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144807 : List Nat := [1, 1, 7, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2144807 : Nat := 118140960795 + 2144807 * 2 ^ 59
def prefixEnd_2144807 : Nat := 4983230072969 + 3 ^ 40 * 2144807 * 2
def baseEnd_2144807 : Nat := 367105634042631722149573

theorem tailTrace_2144807 : CollatzResearch.WordTrace tailWord_2144807 prefixEnd_2144807 367105634042631722149573 := by
  unfold tailWord_2144807
  simp only [CollatzResearch.WordTrace]
  refine ⟨78227537940738017717768675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52151691960492011811845783 78227537940738017717768675)
  ·
    refine ⟨117341306911107026576653013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78227537940738017717768675 117341306911107026576653013)
    ·
      refine ⟨2750186880729070935390305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 117341306911107026576653013 2750186880729070935390305)
      ·
        refine ⟨2062640160546803201542729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2750186880729070935390305 2062640160546803201542729)
        ·
          refine ⟨1546980120410102401157047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2062640160546803201542729 1546980120410102401157047)
          ·
            refine ⟨2320470180615153601735571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546980120410102401157047 2320470180615153601735571)
            ·
              refine ⟨3480705270922730402603357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320470180615153601735571 3480705270922730402603357)
              ·
                refine ⟨1305264476596023900976259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3480705270922730402603357 1305264476596023900976259)
                ·
                  refine ⟨1957896714894035851464389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305264476596023900976259 1957896714894035851464389)
                  ·
                    refine ⟨367105634042631722149573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957896714894035851464389 367105634042631722149573)
                    ·
                      rfl

theorem cell23_2144807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2144807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144807 prefixEnd_2144807 := by exact prefixLift 2144807
  have htrace : WordTrace (prefixWord ++ tailWord_2144807) baseStart_2144807 baseEnd_2144807 := by
    simpa [prefixWord, tailWord_2144807, baseEnd_2144807] using wordTrace_append hprefix tailTrace_2144807
  have hstable : (prefixWord ++ tailWord_2144807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144807).length < 2 ^ (prefixWord ++ tailWord_2144807).sum := by decide
  have hdescent : baseEnd_2144807 < baseStart_2144807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144829 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 4, 4]
def baseStart_2144829 : Nat := 118140960795 + 2144829 * 2 ^ 59
def prefixEnd_2144829 : Nat := 4983230072969 + 3 ^ 40 * 2144829 * 2
def baseEnd_2144829 : Nat := 367109399567431360124539

theorem tailTrace_2144829 : CollatzResearch.WordTrace tailWord_2144829 prefixEnd_2144829 367109399567431360124539 := by
  unfold tailWord_2144829
  simp only [CollatzResearch.WordTrace]
  refine ⟨78228340346658315475069541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52152226897772210316713027 78228340346658315475069541)
  ·
    refine ⟨14667813814998434151575539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78228340346658315475069541 14667813814998434151575539)
    ·
      refine ⟨22001720722497651227363309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14667813814998434151575539 22001720722497651227363309)
      ·
        refine ⟨8250645270936619210261241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22001720722497651227363309 8250645270936619210261241)
        ·
          refine ⟨6187983953202464407695931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8250645270936619210261241 6187983953202464407695931)
          ·
            refine ⟨9281975929803696611543897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6187983953202464407695931 9281975929803696611543897)
            ·
              refine ⟨6961481947352772458657923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9281975929803696611543897 6961481947352772458657923)
              ·
                refine ⟨10442222921029158687986885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6961481947352772458657923 10442222921029158687986885)
                ·
                  refine ⟨1957916797692967253997541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10442222921029158687986885 1957916797692967253997541)
                  ·
                    refine ⟨367109399567431360124539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957916797692967253997541 367109399567431360124539)
                    ·
                      rfl

theorem cell23_2144829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_2144829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144829 prefixEnd_2144829 := by exact prefixLift 2144829
  have htrace : WordTrace (prefixWord ++ tailWord_2144829) baseStart_2144829 baseEnd_2144829 := by
    simpa [prefixWord, tailWord_2144829, baseEnd_2144829] using wordTrace_append hprefix tailTrace_2144829
  have hstable : (prefixWord ++ tailWord_2144829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144829).length < 2 ^ (prefixWord ++ tailWord_2144829).sum := by decide
  have hdescent : baseEnd_2144829 < baseStart_2144829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144830 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2144830 : Nat := 118140960795 + 2144830 * 2 ^ 59
def prefixEnd_2144830 : Nat := 4983230072969 + 3 ^ 40 * 2144830 * 2
def baseEnd_2144830 : Nat := 1101328712182948576461113

theorem tailTrace_2144830 : CollatzResearch.WordTrace tailWord_2144830 prefixEnd_2144830 1101328712182948576461113 := by
  unfold tailWord_2144830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9778547102456836580731993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52152251213103128430570629 9778547102456836580731993)
  ·
    refine ⟨7333910326842627435548995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9778547102456836580731993 7333910326842627435548995)
    ·
      refine ⟨11000865490263941153323493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7333910326842627435548995 11000865490263941153323493)
      ·
        refine ⟨2062662279424488966248155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11000865490263941153323493 2062662279424488966248155)
        ·
          refine ⟨3093993419136733449372233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062662279424488966248155 3093993419136733449372233)
          ·
            refine ⟨2320495064352550087029175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3093993419136733449372233 2320495064352550087029175)
            ·
              refine ⟨3480742596528825130543763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2320495064352550087029175 3480742596528825130543763)
              ·
                refine ⟨5221113894793237695815645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3480742596528825130543763 5221113894793237695815645)
                ·
                  refine ⟨1957917710547464135930867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5221113894793237695815645 1957917710547464135930867)
                  ·
                    refine ⟨2936876565821196203896301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1957917710547464135930867 2936876565821196203896301)
                    ·
                      refine ⟨1101328712182948576461113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2936876565821196203896301 1101328712182948576461113)
                      ·
                        rfl

theorem cell23_2144830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2144830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144830 prefixEnd_2144830 := by exact prefixLift 2144830
  have htrace : WordTrace (prefixWord ++ tailWord_2144830) baseStart_2144830 baseEnd_2144830 := by
    simpa [prefixWord, tailWord_2144830, baseEnd_2144830] using wordTrace_append hprefix tailTrace_2144830
  have hstable : (prefixWord ++ tailWord_2144830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144830).length < 2 ^ (prefixWord ++ tailWord_2144830).sum := by decide
  have hdescent : baseEnd_2144830 < baseStart_2144830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144842 : List Nat := [3, 1, 2, 1, 1, 5, 2, 8]
def baseStart_2144842 : Nat := 118140960795 + 2144842 * 2 ^ 59
def prefixEnd_2144842 : Nat := 4983230072969 + 3 ^ 40 * 2144842 * 2
def baseEnd_2144842 : Nat := 40790180516696389981891

theorem tailTrace_2144842 : CollatzResearch.WordTrace tailWord_2144842 prefixEnd_2144842 40790180516696389981891 := by
  unfold tailWord_2144842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19557203623902804673823195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52152542997074145796861853 19557203623902804673823195)
  ·
    refine ⟨29335805435854207010734793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19557203623902804673823195 29335805435854207010734793)
    ·
      refine ⟨22001854076890655258051095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29335805435854207010734793 22001854076890655258051095)
      ·
        refine ⟨33002781115335982887076643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22001854076890655258051095 33002781115335982887076643)
        ·
          refine ⟨49504171673003974330614965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33002781115335982887076643 49504171673003974330614965)
          ·
            refine ⟨4641016094344122593495153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49504171673003974330614965 4641016094344122593495153)
            ·
              refine ⟨3480762070758091945121365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4641016094344122593495153 3480762070758091945121365)
              ·
                refine ⟨40790180516696389981891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3480762070758091945121365 40790180516696389981891)
                ·
                  rfl

theorem cell23_2144842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_2144842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144842 prefixEnd_2144842 := by exact prefixLift 2144842
  have htrace : WordTrace (prefixWord ++ tailWord_2144842) baseStart_2144842 baseEnd_2144842 := by
    simpa [prefixWord, tailWord_2144842, baseEnd_2144842] using wordTrace_append hprefix tailTrace_2144842
  have hstable : (prefixWord ++ tailWord_2144842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144842).length < 2 ^ (prefixWord ++ tailWord_2144842).sum := by decide
  have hdescent : baseEnd_2144842 < baseStart_2144842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144846 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_2144846 : Nat := 118140960795 + 2144846 * 2 ^ 59
def prefixEnd_2144846 : Nat := 4983230072969 + 3 ^ 40 * 2144846 * 2
def baseEnd_2144846 : Nat := 367112309291140171287013

theorem tailTrace_2144846 : CollatzResearch.WordTrace tailWord_2144846 prefixEnd_2144846 367112309291140171287013 := by
  unfold tailWord_2144846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9778620048449590922304799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52152640258397818252292261 9778620048449590922304799)
  ·
    refine ⟨14667930072674386383457199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9778620048449590922304799 14667930072674386383457199)
    ·
      refine ⟨22001895109011579575185799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14667930072674386383457199 22001895109011579575185799)
      ·
        refine ⟨33002842663517369362778699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22001895109011579575185799 33002842663517369362778699)
        ·
          refine ⟨49504263995276054044168049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33002842663517369362778699 49504263995276054044168049)
          ·
            refine ⟨37128197996457040533126037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49504263995276054044168049 37128197996457040533126037)
            ·
              refine ⟨1740384281083923774990283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37128197996457040533126037 1740384281083923774990283)
              ·
                refine ⟨2610576421625885662485425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740384281083923774990283 2610576421625885662485425)
                ·
                  refine ⟨1957932316219414246864069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2610576421625885662485425 1957932316219414246864069)
                  ·
                    refine ⟨367112309291140171287013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1957932316219414246864069 367112309291140171287013)
                    ·
                      rfl

theorem cell23_2144846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_2144846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144846 prefixEnd_2144846 := by exact prefixLift 2144846
  have htrace : WordTrace (prefixWord ++ tailWord_2144846) baseStart_2144846 baseEnd_2144846 := by
    simpa [prefixWord, tailWord_2144846, baseEnd_2144846] using wordTrace_append hprefix tailTrace_2144846
  have hstable : (prefixWord ++ tailWord_2144846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144846).length < 2 ^ (prefixWord ++ tailWord_2144846).sum := by decide
  have hdescent : baseEnd_2144846 < baseStart_2144846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144892 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_2144892 : Nat := 118140960795 + 2144892 * 2 ^ 59
def prefixEnd_2144892 : Nat := 4983230072969 + 3 ^ 40 * 2144892 * 2
def baseEnd_2144892 : Nat := 1101360547983527333885827

theorem tailTrace_2144892 : CollatzResearch.WordTrace tailWord_2144892 prefixEnd_2144892 1101360547983527333885827 := by
  unfold tailWord_2144892
  simp only [CollatzResearch.WordTrace]
  refine ⟨39115319072715038617306465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52153758763620051489741953 39115319072715038617306465)
  ·
    refine ⟨29336489304536278962979849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39115319072715038617306465 29336489304536278962979849)
    ·
      refine ⟨22002366978402209222234887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29336489304536278962979849 22002366978402209222234887)
      ·
        refine ⟨33003550467603313833352331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22002366978402209222234887 33003550467603313833352331)
        ·
          refine ⟨49505325701404970750028497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33003550467603313833352331 49505325701404970750028497)
          ·
            refine ⟨37128994276053728062521373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49505325701404970750028497 37128994276053728062521373)
            ·
              refine ⟨13923372853520148023445515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37128994276053728062521373 13923372853520148023445515)
              ·
                refine ⟨20885059280280222035168273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13923372853520148023445515 20885059280280222035168273)
                ·
                  refine ⟨15663794460210166526376205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20885059280280222035168273 15663794460210166526376205)
                  ·
                    refine ⟨5873922922578812447391077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15663794460210166526376205 5873922922578812447391077)
                    ·
                      refine ⟨1101360547983527333885827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5873922922578812447391077 1101360547983527333885827)
                      ·
                        rfl

theorem cell23_2144892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_2144892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144892 prefixEnd_2144892 := by exact prefixLift 2144892
  have htrace : WordTrace (prefixWord ++ tailWord_2144892) baseStart_2144892 baseEnd_2144892 := by
    simpa [prefixWord, tailWord_2144892, baseEnd_2144892] using wordTrace_append hprefix tailTrace_2144892
  have hstable : (prefixWord ++ tailWord_2144892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144892).length < 2 ^ (prefixWord ++ tailWord_2144892).sum := by decide
  have hdescent : baseEnd_2144892 < baseStart_2144892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144932 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 9]
def baseStart_2144932 : Nat := 118140960795 + 2144932 * 2 ^ 59
def prefixEnd_2144932 : Nat := 4983230072969 + 3 ^ 40 * 2144932 * 2
def baseEnd_2144932 : Nat := 122375676356634130820627

theorem tailTrace_2144932 : CollatzResearch.WordTrace tailWord_2144932 prefixEnd_2144932 122375676356634130820627 := by
  unfold tailWord_2144932
  simp only [CollatzResearch.WordTrace]
  refine ⟨39116048532642582033034525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52154731376856776044046033 39116048532642582033034525)
  ·
    refine ⟨14668518199740968262387947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39116048532642582033034525 14668518199740968262387947)
    ·
      refine ⟨22002777299611452393581921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14668518199740968262387947 22002777299611452393581921)
      ·
        refine ⟨16502082974708589295186441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22002777299611452393581921 16502082974708589295186441)
        ·
          refine ⟨12376562231031441971389831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16502082974708589295186441 12376562231031441971389831)
          ·
            refine ⟨18564843346547162957084747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12376562231031441971389831 18564843346547162957084747)
            ·
              refine ⟨27847265019820744435627121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18564843346547162957084747 27847265019820744435627121)
              ·
                refine ⟨20885448764865558326720341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27847265019820744435627121 20885448764865558326720341)
                ·
                  refine ⟨122375676356634130820627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20885448764865558326720341 122375676356634130820627)
                  ·
                    rfl

theorem cell23_2144932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_2144932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144932 prefixEnd_2144932 := by exact prefixLift 2144932
  have htrace : WordTrace (prefixWord ++ tailWord_2144932) baseStart_2144932 baseEnd_2144932 := by
    simpa [prefixWord, tailWord_2144932, baseEnd_2144932] using wordTrace_append hprefix tailTrace_2144932
  have hstable : (prefixWord ++ tailWord_2144932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144932).length < 2 ^ (prefixWord ++ tailWord_2144932).sum := by decide
  have hdescent : baseEnd_2144932 < baseStart_2144932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144943 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 2, 2, 2]
def baseStart_2144943 : Nat := 118140960795 + 2144943 * 2 ^ 59
def prefixEnd_2144943 : Nat := 4983230072969 + 3 ^ 40 * 2144943 * 2
def baseEnd_2144943 : Nat := 1101386735496906634348093

theorem tailTrace_2144943 : CollatzResearch.WordTrace tailWord_2144943 prefixEnd_2144943 1101386735496906634348093 := by
  unfold tailWord_2144943
  simp only [CollatzResearch.WordTrace]
  refine ⟨78232498268245312944719483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52154998845496875296479655 78232498268245312944719483)
  ·
    refine ⟨117348747402367969417079225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78232498268245312944719483 117348747402367969417079225)
    ·
      refine ⟨88011560551775977062809419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117348747402367969417079225 88011560551775977062809419)
      ·
        refine ⟨132017340827663965594214129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88011560551775977062809419 132017340827663965594214129)
        ·
          refine ⟨99013005620747974195660597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132017340827663965594214129 99013005620747974195660597)
          ·
            refine ⟨9282469276945122580843181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99013005620747974195660597 9282469276945122580843181)
            ·
              refine ⟨3480925978854420967816193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9282469276945122580843181 3480925978854420967816193)
              ·
                refine ⟨2610694484140815725862145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3480925978854420967816193 2610694484140815725862145)
                ·
                  refine ⟨1958020863105611794396609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2610694484140815725862145 1958020863105611794396609)
                  ·
                    refine ⟨1468515647329208845797457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1958020863105611794396609 1468515647329208845797457)
                    ·
                      refine ⟨1101386735496906634348093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468515647329208845797457 1101386735496906634348093)
                      ·
                        rfl

theorem cell23_2144943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 2, 2].length) (baseStart_2144943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144943 prefixEnd_2144943 := by exact prefixLift 2144943
  have htrace : WordTrace (prefixWord ++ tailWord_2144943) baseStart_2144943 baseEnd_2144943 := by
    simpa [prefixWord, tailWord_2144943, baseEnd_2144943] using wordTrace_append hprefix tailTrace_2144943
  have hstable : (prefixWord ++ tailWord_2144943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144943).length < 2 ^ (prefixWord ++ tailWord_2144943).sum := by decide
  have hdescent : baseEnd_2144943 < baseStart_2144943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144949 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 7]
def baseStart_2144949 : Nat := 118140960795 + 2144949 * 2 ^ 59
def prefixEnd_2144949 : Nat := 4983230072969 + 3 ^ 40 * 2144949 * 2
def baseEnd_2144949 : Nat := 122376646264537067874785

theorem tailTrace_2144949 : CollatzResearch.WordTrace tailWord_2144949 prefixEnd_2144949 122376646264537067874785 := by
  unfold tailWord_2144949
  simp only [CollatzResearch.WordTrace]
  refine ⟨78232717106223575969437901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52155144737482383979625267 78232717106223575969437901)
  ·
    refine ⟨29337268914833840988539213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78232717106223575969437901 29337268914833840988539213)
    ·
      refine ⟨11001475843062690370702205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29337268914833840988539213 11001475843062690370702205)
      ·
        refine ⟨4125553441148508889013327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11001475843062690370702205 4125553441148508889013327)
        ·
          refine ⟨6188330161722763333519991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4125553441148508889013327 6188330161722763333519991)
          ·
            refine ⟨9282495242584145000279987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6188330161722763333519991 9282495242584145000279987)
            ·
              refine ⟨13923742863876217500419981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9282495242584145000279987 13923742863876217500419981)
              ·
                refine ⟨5221403573953581562657493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13923742863876217500419981 5221403573953581562657493)
                ·
                  refine ⟨122376646264537067874785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5221403573953581562657493 122376646264537067874785)
                  ·
                    rfl

theorem cell23_2144949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 7].length) (baseStart_2144949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144949 prefixEnd_2144949 := by exact prefixLift 2144949
  have htrace : WordTrace (prefixWord ++ tailWord_2144949) baseStart_2144949 baseEnd_2144949 := by
    simpa [prefixWord, tailWord_2144949, baseEnd_2144949] using wordTrace_append hprefix tailTrace_2144949
  have hstable : (prefixWord ++ tailWord_2144949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144949).length < 2 ^ (prefixWord ++ tailWord_2144949).sum := by decide
  have hdescent : baseEnd_2144949 < baseStart_2144949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144959 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 3]
def baseStart_2144959 : Nat := 118140960795 + 2144959 * 2 ^ 59
def prefixEnd_2144959 : Nat := 4983230072969 + 3 ^ 40 * 2144959 * 2
def baseEnd_2144959 : Nat := 1101394951187378571748019

theorem tailTrace_2144959 : CollatzResearch.WordTrace tailWord_2144959 prefixEnd_2144959 1101394951187378571748019 := by
  unfold tailWord_2144959
  simp only [CollatzResearch.WordTrace]
  refine ⟨78233081836187347677301931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52155387890791565118201287 78233081836187347677301931)
  ·
    refine ⟨117349622754281021515952897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78233081836187347677301931 117349622754281021515952897)
    ·
      refine ⟨88012217065710766136964673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117349622754281021515952897 88012217065710766136964673)
      ·
        refine ⟨66009162799283074602723505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88012217065710766136964673 66009162799283074602723505)
        ·
          refine ⟨49506872099462305952042629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66009162799283074602723505 49506872099462305952042629)
          ·
            refine ⟨9282538518649182366007993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49506872099462305952042629 9282538518649182366007993)
            ·
              refine ⟨6961903888986886774505995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9282538518649182366007993 6961903888986886774505995)
              ·
                refine ⟨10442855833480330161758993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6961903888986886774505995 10442855833480330161758993)
                ·
                  refine ⟨7832141875110247621319245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10442855833480330161758993 7832141875110247621319245)
                  ·
                    refine ⟨2937053203166342857994717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7832141875110247621319245 2937053203166342857994717)
                    ·
                      refine ⟨1101394951187378571748019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2937053203166342857994717 1101394951187378571748019)
                      ·
                        rfl

theorem cell23_2144959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_2144959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144959 prefixEnd_2144959 := by exact prefixLift 2144959
  have htrace : WordTrace (prefixWord ++ tailWord_2144959) baseStart_2144959 baseEnd_2144959 := by
    simpa [prefixWord, tailWord_2144959, baseEnd_2144959] using wordTrace_append hprefix tailTrace_2144959
  have hstable : (prefixWord ++ tailWord_2144959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144959).length < 2 ^ (prefixWord ++ tailWord_2144959).sum := by decide
  have hdescent : baseEnd_2144959 < baseStart_2144959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2144960 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 2, 2, 2]
def baseStart_2144960 : Nat := 118140960795 + 2144960 * 2 ^ 59
def prefixEnd_2144960 : Nat := 4983230072969 + 3 ^ 40 * 2144960 * 2
def baseEnd_2144960 : Nat := 1101395464668033067835515

theorem tailTrace_2144960 : CollatzResearch.WordTrace tailWord_2144960 prefixEnd_2144960 1101395464668033067835515 := by
  unfold tailWord_2144960
  simp only [CollatzResearch.WordTrace]
  refine ⟨39116559154591862424044167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52155412206122483232058889 39116559154591862424044167)
  ·
    refine ⟨58674838731887793636066251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39116559154591862424044167 58674838731887793636066251)
    ·
      refine ⟨88012258097831690454099377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58674838731887793636066251 88012258097831690454099377)
      ·
        refine ⟨66009193573373767840574533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88012258097831690454099377 66009193573373767840574533)
        ·
          refine ⟨12376723795007581470107725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66009193573373767840574533 12376723795007581470107725)
          ·
            refine ⟨4641271423127843051290397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12376723795007581470107725 4641271423127843051290397)
            ·
              refine ⟨1740476783672941144233899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4641271423127843051290397 1740476783672941144233899)
              ·
                refine ⟨2610715175509411716350849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740476783672941144233899 2610715175509411716350849)
                ·
                  refine ⟨1958036381632058787263137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2610715175509411716350849 1958036381632058787263137)
                  ·
                    refine ⟨1468527286224044090447353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1958036381632058787263137 1468527286224044090447353)
                    ·
                      refine ⟨1101395464668033067835515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468527286224044090447353 1101395464668033067835515)
                      ·
                        rfl

theorem cell23_2144960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_2144960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2144960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2144960 prefixEnd_2144960 := by exact prefixLift 2144960
  have htrace : WordTrace (prefixWord ++ tailWord_2144960) baseStart_2144960 baseEnd_2144960 := by
    simpa [prefixWord, tailWord_2144960, baseEnd_2144960] using wordTrace_append hprefix tailTrace_2144960
  have hstable : (prefixWord ++ tailWord_2144960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2144960).length < 2 ^ (prefixWord ++ tailWord_2144960).sum := by decide
  have hdescent : baseEnd_2144960 < baseStart_2144960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2144960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145056 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 6]
def baseStart_2145056 : Nat := 118140960795 + 2145056 * 2 ^ 59
def prefixEnd_2145056 : Nat := 4983230072969 + 3 ^ 40 * 2145056 * 2
def baseEnd_2145056 : Nat := 122382750978984965803897

theorem tailTrace_2145056 : CollatzResearch.WordTrace tailWord_2145056 prefixEnd_2145056 122382750978984965803897 := by
  unfold tailWord_2145056
  simp only [CollatzResearch.WordTrace]
  refine ⟨39118309858417966621791511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52157746477890622162388681 39118309858417966621791511)
  ·
    refine ⟨58677464787626949932687267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39118309858417966621791511 58677464787626949932687267)
    ·
      refine ⟨88016197181440424899030901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58677464787626949932687267 88016197181440424899030901)
      ·
        refine ⟨8251518485760039834284147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88016197181440424899030901 8251518485760039834284147)
        ·
          refine ⟨12377277728640059751426221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8251518485760039834284147 12377277728640059751426221)
          ·
            refine ⟨4641479148240022406784833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12377277728640059751426221 4641479148240022406784833)
            ·
              refine ⟨3481109361180016805088625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4641479148240022406784833 3481109361180016805088625)
              ·
                refine ⟨2610832020885012603816469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481109361180016805088625 2610832020885012603816469)
                ·
                  refine ⟨122382750978984965803897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2610832020885012603816469 122382750978984965803897)
                  ·
                    rfl

theorem cell23_2145056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 6].length) (baseStart_2145056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145056 prefixEnd_2145056 := by exact prefixLift 2145056
  have htrace : WordTrace (prefixWord ++ tailWord_2145056) baseStart_2145056 baseEnd_2145056 := by
    simpa [prefixWord, tailWord_2145056, baseEnd_2145056] using wordTrace_append hprefix tailTrace_2145056
  have hstable : (prefixWord ++ tailWord_2145056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145056).length < 2 ^ (prefixWord ++ tailWord_2145056).sum := by decide
  have hdescent : baseEnd_2145056 < baseStart_2145056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145060 : List Nat := [2, 3, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_2145060 : Nat := 118140960795 + 2145060 * 2 ^ 59
def prefixEnd_2145060 : Nat := 4983230072969 + 3 ^ 40 * 2145060 * 2
def baseEnd_2145060 : Nat := 367148937577827558861685

theorem tailTrace_2145060 : CollatzResearch.WordTrace tailWord_2145060 prefixEnd_2145060 367148937577827558861685 := by
  unfold tailWord_2145060
  simp only [CollatzResearch.WordTrace]
  refine ⟨39118382804410720963364317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52157843739214294617819089 39118382804410720963364317)
  ·
    refine ⟨14669393551654020361261619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39118382804410720963364317 14669393551654020361261619)
    ·
      refine ⟨22004090327481030541892429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14669393551654020361261619 22004090327481030541892429)
      ·
        refine ⟨8251533872805386453209661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22004090327481030541892429 8251533872805386453209661)
        ·
          refine ⟨3094325202302019919953623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8251533872805386453209661 3094325202302019919953623)
          ·
            refine ⟨4641487803453029879930435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094325202302019919953623 4641487803453029879930435)
            ·
              refine ⟨6962231705179544819895653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4641487803453029879930435 6962231705179544819895653)
              ·
                refine ⟨1305418444721164653730435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6962231705179544819895653 1305418444721164653730435)
                ·
                  refine ⟨1958127667081746980595653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305418444721164653730435 1958127667081746980595653)
                  ·
                    refine ⟨367148937577827558861685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958127667081746980595653 367148937577827558861685)
                    ·
                      rfl

theorem cell23_2145060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_2145060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145060 prefixEnd_2145060 := by exact prefixLift 2145060
  have htrace : WordTrace (prefixWord ++ tailWord_2145060) baseStart_2145060 baseEnd_2145060 := by
    simpa [prefixWord, tailWord_2145060, baseEnd_2145060] using wordTrace_append hprefix tailTrace_2145060
  have hstable : (prefixWord ++ tailWord_2145060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145060).length < 2 ^ (prefixWord ++ tailWord_2145060).sum := by decide
  have hdescent : baseEnd_2145060 < baseStart_2145060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145094 : List Nat := [6, 1, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2145094 : Nat := 118140960795 + 2145094 * 2 ^ 59
def prefixEnd_2145094 : Nat := 4983230072969 + 3 ^ 40 * 2145094 * 2
def baseEnd_2145094 : Nat := 367154757025245181186633

theorem tailTrace_2145094 : CollatzResearch.WordTrace tailWord_2145094 prefixEnd_2145094 367154757025245181186633 := by
  unfold tailWord_2145094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444937677834320804170823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52158670460465510488977557 2444937677834320804170823)
  ·
    refine ⟨3667406516751481206256235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2444937677834320804170823 3667406516751481206256235)
    ·
      refine ⟨5501109775127221809384353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3667406516751481206256235 5501109775127221809384353)
      ·
        refine ⟨4125832331345416357038265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5501109775127221809384353 4125832331345416357038265)
        ·
          refine ⟨3094374248509062267778699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4125832331345416357038265 3094374248509062267778699)
          ·
            refine ⟨4641561372763593401668049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094374248509062267778699 4641561372763593401668049)
            ·
              refine ⟨3481171029572695051251037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4641561372763593401668049 3481171029572695051251037)
              ·
                refine ⟨1305439136089760644219139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3481171029572695051251037 1305439136089760644219139)
                ·
                  refine ⟨1958158704134640966328709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305439136089760644219139 1958158704134640966328709)
                  ·
                    refine ⟨367154757025245181186633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958158704134640966328709 367154757025245181186633)
                    ·
                      rfl

theorem cell23_2145094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2145094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145094 prefixEnd_2145094 := by exact prefixLift 2145094
  have htrace : WordTrace (prefixWord ++ tailWord_2145094) baseStart_2145094 baseEnd_2145094 := by
    simpa [prefixWord, tailWord_2145094, baseEnd_2145094] using wordTrace_append hprefix tailTrace_2145094
  have hstable : (prefixWord ++ tailWord_2145094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145094).length < 2 ^ (prefixWord ++ tailWord_2145094).sum := by decide
  have hdescent : baseEnd_2145094 < baseStart_2145094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145100 : List Nat := [2, 2, 1, 3, 3, 1, 1, 5, 1, 1, 3]
def baseStart_2145100 : Nat := 118140960795 + 2145100 * 2 ^ 59
def prefixEnd_2145100 : Nat := 4983230072969 + 3 ^ 40 * 2145100 * 2
def baseEnd_2145100 : Nat := 1101467351959662520084871

theorem tailTrace_2145100 : CollatzResearch.WordTrace tailWord_2145100 prefixEnd_2145100 1101467351959662520084871 := by
  unfold tailWord_2145100
  simp only [CollatzResearch.WordTrace]
  refine ⟨39119112264338264379092377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52158816352451019172123169 39119112264338264379092377)
  ·
    refine ⟨29339334198253698284319283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39119112264338264379092377 29339334198253698284319283)
    ·
      refine ⟨44009001297380547426478925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29339334198253698284319283 44009001297380547426478925)
      ·
        refine ⟨16503375486517705284929597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44009001297380547426478925 16503375486517705284929597)
        ·
          refine ⟨6188765807444139481848599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16503375486517705284929597 6188765807444139481848599)
          ·
            refine ⟨9283148711166209222772899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6188765807444139481848599 9283148711166209222772899)
            ·
              refine ⟨13924723066749313834159349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9283148711166209222772899 13924723066749313834159349)
              ·
                refine ⟨1305442787507748171952439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13924723066749313834159349 1305442787507748171952439)
                ·
                  refine ⟨1958164181261622257928659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305442787507748171952439 1958164181261622257928659)
                  ·
                    refine ⟨2937246271892433386892989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1958164181261622257928659 2937246271892433386892989)
                    ·
                      refine ⟨1101467351959662520084871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2937246271892433386892989 1101467351959662520084871)
                      ·
                        rfl

theorem cell23_2145100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_2145100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145100 prefixEnd_2145100 := by exact prefixLift 2145100
  have htrace : WordTrace (prefixWord ++ tailWord_2145100) baseStart_2145100 baseEnd_2145100 := by
    simpa [prefixWord, tailWord_2145100, baseEnd_2145100] using wordTrace_append hprefix tailTrace_2145100
  have hstable : (prefixWord ++ tailWord_2145100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145100).length < 2 ^ (prefixWord ++ tailWord_2145100).sum := by decide
  have hdescent : baseEnd_2145100 < baseStart_2145100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145119 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_2145119 : Nat := 118140960795 + 2145119 * 2 ^ 59
def prefixEnd_2145119 : Nat := 4983230072969 + 3 ^ 40 * 2145119 * 2
def baseEnd_2145119 : Nat := 1101477108092097945747283

theorem tailTrace_2145119 : CollatzResearch.WordTrace tailWord_2145119 prefixEnd_2145119 1101477108092097945747283 := by
  unfold tailWord_2145119
  simp only [CollatzResearch.WordTrace]
  refine ⟨78238917515607695003126411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52159278343738463335417607 78238917515607695003126411)
  ·
    refine ⟨117358376273411542504689617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78238917515607695003126411 117358376273411542504689617)
    ·
      refine ⟨88018782205058656878517213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117358376273411542504689617 88018782205058656878517213)
      ·
        refine ⟨33007043326896996329443955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88018782205058656878517213 33007043326896996329443955)
        ·
          refine ⟨49510564990345494494165933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33007043326896996329443955 49510564990345494494165933)
          ·
            refine ⟨18566461871379560435312225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49510564990345494494165933 18566461871379560435312225)
            ·
              refine ⟨13924846403534670326484169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18566461871379560435312225 13924846403534670326484169)
              ·
                refine ⟨10443634802651002744863127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13924846403534670326484169 10443634802651002744863127)
                ·
                  refine ⟨15665452203976504117294691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10443634802651002744863127 15665452203976504117294691)
                  ·
                    refine ⟨23498178305964756175942037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15665452203976504117294691 23498178305964756175942037)
                    ·
                      refine ⟨1101477108092097945747283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23498178305964756175942037 1101477108092097945747283)
                      ·
                        rfl

theorem cell23_2145119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_2145119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145119 prefixEnd_2145119 := by exact prefixLift 2145119
  have htrace : WordTrace (prefixWord ++ tailWord_2145119) baseStart_2145119 baseEnd_2145119 := by
    simpa [prefixWord, tailWord_2145119, baseEnd_2145119] using wordTrace_append hprefix tailTrace_2145119
  have hstable : (prefixWord ++ tailWord_2145119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145119).length < 2 ^ (prefixWord ++ tailWord_2145119).sum := by decide
  have hdescent : baseEnd_2145119 < baseStart_2145119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145136 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4]
def baseStart_2145136 : Nat := 118140960795 + 2145136 * 2 ^ 59
def prefixEnd_2145136 : Nat := 4983230072969 + 3 ^ 40 * 2145136 * 2
def baseEnd_2145136 : Nat := 1101485837263224379234705

theorem tailTrace_2145136 : CollatzResearch.WordTrace tailWord_2145136 prefixEnd_2145136 1101485837263224379234705 := by
  unfold tailWord_2145136
  simp only [CollatzResearch.WordTrace]
  refine ⟨39119768778273053453247631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52159691704364071270996841 39119768778273053453247631)
  ·
    refine ⟨58679653167409580179871447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39119768778273053453247631 58679653167409580179871447)
    ·
      refine ⟨88019479751114370269807171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58679653167409580179871447 88019479751114370269807171)
      ·
        refine ⟨132029219626671555404710757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88019479751114370269807171 132029219626671555404710757)
        ·
          refine ⟨24755478680000916638383267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132029219626671555404710757 24755478680000916638383267)
          ·
            refine ⟨37133218020001374957574901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24755478680000916638383267 37133218020001374957574901)
            ·
              refine ⟨3481239189375128902272647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37133218020001374957574901 3481239189375128902272647)
              ·
                refine ⟨5221858784062693353408971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481239189375128902272647 5221858784062693353408971)
                ·
                  refine ⟨7832788176094040030113457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5221858784062693353408971 7832788176094040030113457)
                  ·
                    refine ⟨5874591132070530022585093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7832788176094040030113457 5874591132070530022585093)
                    ·
                      refine ⟨1101485837263224379234705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5874591132070530022585093 1101485837263224379234705)
                      ·
                        rfl

theorem cell23_2145136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_2145136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145136 prefixEnd_2145136 := by exact prefixLift 2145136
  have htrace : WordTrace (prefixWord ++ tailWord_2145136) baseStart_2145136 baseEnd_2145136 := by
    simpa [prefixWord, tailWord_2145136, baseEnd_2145136] using wordTrace_append hprefix tailTrace_2145136
  have hstable : (prefixWord ++ tailWord_2145136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145136).length < 2 ^ (prefixWord ++ tailWord_2145136).sum := by decide
  have hdescent : baseEnd_2145136 < baseStart_2145136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145156 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_2145156 : Nat := 118140960795 + 2145156 * 2 ^ 59
def prefixEnd_2145156 : Nat := 4983230072969 + 3 ^ 40 * 2145156 * 2
def baseEnd_2145156 : Nat := 1101496106876314300984613

theorem tailTrace_2145156 : CollatzResearch.WordTrace tailWord_2145156 prefixEnd_2145156 1101496106876314300984613 := by
  unfold tailWord_2145156
  simp only [CollatzResearch.WordTrace]
  refine ⟨39120133508236825161111661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52160178010982433548148881 39120133508236825161111661)
  ·
    refine ⟨14670050065588809435416873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39120133508236825161111661 14670050065588809435416873)
    ·
      refine ⟨11002537549191607076562655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14670050065588809435416873 11002537549191607076562655)
      ·
        refine ⟨16503806323787410614843983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11002537549191607076562655 16503806323787410614843983)
        ·
          refine ⟨24755709485681115922265975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16503806323787410614843983 24755709485681115922265975)
          ·
            refine ⟨37133564228521673883398963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24755709485681115922265975 37133564228521673883398963)
            ·
              refine ⟨55700346342782510825098445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37133564228521673883398963 55700346342782510825098445)
              ·
                refine ⟨20887629878543441559411917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55700346342782510825098445 20887629878543441559411917)
                ·
                  refine ⟨7832861204453790584779469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20887629878543441559411917 7832861204453790584779469)
                  ·
                    refine ⟨2937322951670171469292301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7832861204453790584779469 2937322951670171469292301)
                    ·
                      refine ⟨1101496106876314300984613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2937322951670171469292301 1101496106876314300984613)
                      ·
                        rfl

theorem cell23_2145156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_2145156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145156 prefixEnd_2145156 := by exact prefixLift 2145156
  have htrace : WordTrace (prefixWord ++ tailWord_2145156) baseStart_2145156 baseEnd_2145156 := by
    simpa [prefixWord, tailWord_2145156, baseEnd_2145156] using wordTrace_append hprefix tailTrace_2145156
  have hstable : (prefixWord ++ tailWord_2145156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145156).length < 2 ^ (prefixWord ++ tailWord_2145156).sum := by decide
  have hdescent : baseEnd_2145156 < baseStart_2145156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145157 : List Nat := [1, 3, 1, 1, 3, 3, 3, 3, 1, 2, 2]
def baseStart_2145157 : Nat := 118140960795 + 2145157 * 2 ^ 59
def prefixEnd_2145157 : Nat := 4983230072969 + 3 ^ 40 * 2145157 * 2
def baseEnd_2145157 : Nat := 1101496620356968797072109

theorem tailTrace_2145157 : CollatzResearch.WordTrace tailWord_2145157 prefixEnd_2145157 1101496620356968797072109 := by
  unfold tailWord_2145157
  simp only [CollatzResearch.WordTrace]
  refine ⟨78240303489470027493009725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52160202326313351662006483 78240303489470027493009725)
  ·
    refine ⟨29340113808551260309878647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78240303489470027493009725 29340113808551260309878647)
    ·
      refine ⟨44010170712826890464817971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29340113808551260309878647 44010170712826890464817971)
      ·
        refine ⟨66015256069240335697226957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44010170712826890464817971 66015256069240335697226957)
        ·
          refine ⟨24755721025965125886460109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66015256069240335697226957 24755721025965125886460109)
          ·
            refine ⟨9283395384736922207422541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24755721025965125886460109 9283395384736922207422541)
            ·
              refine ⟨3481273269276345827783453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9283395384736922207422541 3481273269276345827783453)
              ·
                refine ⟨1305477475978629685418795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3481273269276345827783453 1305477475978629685418795)
                ·
                  refine ⟨1958216213967944528128193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305477475978629685418795 1958216213967944528128193)
                  ·
                    refine ⟨1468662160475958396096145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1958216213967944528128193 1468662160475958396096145)
                    ·
                      refine ⟨1101496620356968797072109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468662160475958396096145 1101496620356968797072109)
                      ·
                        rfl

theorem cell23_2145157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_2145157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145157 prefixEnd_2145157 := by exact prefixLift 2145157
  have htrace : WordTrace (prefixWord ++ tailWord_2145157) baseStart_2145157 baseEnd_2145157 := by
    simpa [prefixWord, tailWord_2145157, baseEnd_2145157] using wordTrace_append hprefix tailTrace_2145157
  have hstable : (prefixWord ++ tailWord_2145157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145157).length < 2 ^ (prefixWord ++ tailWord_2145157).sum := by decide
  have hdescent : baseEnd_2145157 < baseStart_2145157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145169 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2145169 : Nat := 118140960795 + 2145169 * 2 ^ 59
def prefixEnd_2145169 : Nat := 4983230072969 + 3 ^ 40 * 2145169 * 2
def baseEnd_2145169 : Nat := 1101502782124822750122053

theorem tailTrace_2145169 : CollatzResearch.WordTrace tailWord_2145169 prefixEnd_2145169 1101502782124822750122053 := by
  unfold tailWord_2145169
  simp only [CollatzResearch.WordTrace]
  refine ⟨78240741165426553542446561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52160494110284369028297707 78240741165426553542446561)
  ·
    refine ⟨58680555874069915156834921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78240741165426553542446561 58680555874069915156834921)
    ·
      refine ⟨44010416905552436367626191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58680555874069915156834921 44010416905552436367626191)
      ·
        refine ⟨66015625358328654551439287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44010416905552436367626191 66015625358328654551439287)
        ·
          refine ⟨99023438037492981827158931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66015625358328654551439287 99023438037492981827158931)
          ·
            refine ⟨148535157056239472740738397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99023438037492981827158931 148535157056239472740738397)
            ·
              refine ⟨55700683896089802277776899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148535157056239472740738397 55700683896089802277776899)
              ·
                refine ⟨83551025844134703416665349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55700683896089802277776899 83551025844134703416665349)
                ·
                  refine ⟨15665817345775256890624753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83551025844134703416665349 15665817345775256890624753)
                  ·
                    refine ⟨11749363009331442667968565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15665817345775256890624753 11749363009331442667968565)
                    ·
                      refine ⟨1101502782124822750122053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11749363009331442667968565 1101502782124822750122053)
                      ·
                        rfl

theorem cell23_2145169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2145169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145169 prefixEnd_2145169 := by exact prefixLift 2145169
  have htrace : WordTrace (prefixWord ++ tailWord_2145169) baseStart_2145169 baseEnd_2145169 := by
    simpa [prefixWord, tailWord_2145169, baseEnd_2145169] using wordTrace_append hprefix tailTrace_2145169
  have hstable : (prefixWord ++ tailWord_2145169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145169).length < 2 ^ (prefixWord ++ tailWord_2145169).sum := by decide
  have hdescent : baseEnd_2145169 < baseStart_2145169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145173 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_2145173 : Nat := 118140960795 + 2145173 * 2 ^ 59
def prefixEnd_2145173 : Nat := 4983230072969 + 3 ^ 40 * 2145173 * 2
def baseEnd_2145173 : Nat := 1101504836047440734472035

theorem tailTrace_2145173 : CollatzResearch.WordTrace tailWord_2145173 prefixEnd_2145173 1101504836047440734472035 := by
  unfold tailWord_2145173
  simp only [CollatzResearch.WordTrace]
  refine ⟨78240887057412062225592173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52160591371608041483728115 78240887057412062225592173)
  ·
    refine ⟨29340332646529523334597065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78240887057412062225592173 29340332646529523334597065)
    ·
      refine ⟨22005249484897142500947799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29340332646529523334597065 22005249484897142500947799)
      ·
        refine ⟨33007874227345713751421699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22005249484897142500947799 33007874227345713751421699)
        ·
          refine ⟨49511811341018570627132549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33007874227345713751421699 49511811341018570627132549)
          ·
            refine ⟨9283464626440981992587353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49511811341018570627132549 9283464626440981992587353)
            ·
              refine ⟨6962598469830736494440515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9283464626440981992587353 6962598469830736494440515)
              ·
                refine ⟨10443897704746104741660773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6962598469830736494440515 10443897704746104741660773)
                ·
                  refine ⟨1958230819639894639061395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10443897704746104741660773 1958230819639894639061395)
                  ·
                    refine ⟨2937346229459841958592093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1958230819639894639061395 2937346229459841958592093)
                    ·
                      refine ⟨1101504836047440734472035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2937346229459841958592093 1101504836047440734472035)
                      ·
                        rfl

theorem cell23_2145173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_2145173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145173 prefixEnd_2145173 := by exact prefixLift 2145173
  have htrace : WordTrace (prefixWord ++ tailWord_2145173) baseStart_2145173 baseEnd_2145173 := by
    simpa [prefixWord, tailWord_2145173, baseEnd_2145173] using wordTrace_append hprefix tailTrace_2145173
  have hstable : (prefixWord ++ tailWord_2145173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145173).length < 2 ^ (prefixWord ++ tailWord_2145173).sum := by decide
  have hdescent : baseEnd_2145173 < baseStart_2145173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145216 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_2145216 : Nat := 118140960795 + 2145216 * 2 ^ 59
def prefixEnd_2145216 : Nat := 4983230072969 + 3 ^ 40 * 2145216 * 2
def baseEnd_2145216 : Nat := 1101526915715584066234337

theorem tailTrace_2145216 : CollatzResearch.WordTrace tailWord_2145216 prefixEnd_2145216 1101526915715584066234337 := by
  unfold tailWord_2145216
  simp only [CollatzResearch.WordTrace]
  refine ⟨39121227698128140284703751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52161636930837520379605001 39121227698128140284703751)
  ·
    refine ⟨58681841547192210427055627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39121227698128140284703751 58681841547192210427055627)
    ·
      refine ⟨88022762320788315640583441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58681841547192210427055627 88022762320788315640583441)
      ·
        refine ⟨66017071740591236730437581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88022762320788315640583441 66017071740591236730437581)
        ·
          refine ⟨24756401902721713773914093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66017071740591236730437581 24756401902721713773914093)
          ·
            refine ⟨9283650713520642665217785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24756401902721713773914093 9283650713520642665217785)
            ·
              refine ⟨6962738035140481998913339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9283650713520642665217785 6962738035140481998913339)
              ·
                refine ⟨10444107052710722998370009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6962738035140481998913339 10444107052710722998370009)
                ·
                  refine ⟨7833080289533042248777507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10444107052710722998370009 7833080289533042248777507)
                  ·
                    refine ⟨11749620434299563373166261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7833080289533042248777507 11749620434299563373166261)
                    ·
                      refine ⟨1101526915715584066234337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11749620434299563373166261 1101526915715584066234337)
                      ·
                        rfl

theorem cell23_2145216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_2145216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145216 prefixEnd_2145216 := by exact prefixLift 2145216
  have htrace : WordTrace (prefixWord ++ tailWord_2145216) baseStart_2145216 baseEnd_2145216 := by
    simpa [prefixWord, tailWord_2145216, baseEnd_2145216] using wordTrace_append hprefix tailTrace_2145216
  have hstable : (prefixWord ++ tailWord_2145216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145216).length < 2 ^ (prefixWord ++ tailWord_2145216).sum := by decide
  have hdescent : baseEnd_2145216 < baseStart_2145216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145219 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 9]
def baseStart_2145219 : Nat := 118140960795 + 2145219 * 2 ^ 59
def prefixEnd_2145219 : Nat := 4983230072969 + 3 ^ 40 * 2145219 * 2
def baseEnd_2145219 : Nat := 122392050684171950499647

theorem tailTrace_2145219 : CollatzResearch.WordTrace tailWord_2145219 prefixEnd_2145219 122392050684171950499647 := by
  unfold tailWord_2145219
  simp only [CollatzResearch.WordTrace]
  refine ⟨78242564815245412081766711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52161709876830274721177807 78242564815245412081766711)
  ·
    refine ⟨117363847222868118122650067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78242564815245412081766711 117363847222868118122650067)
    ·
      refine ⟨176045770834302177183975101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117363847222868118122650067 176045770834302177183975101)
      ·
        refine ⟨66017164062863316443990663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176045770834302177183975101 66017164062863316443990663)
        ·
          refine ⟨99025746094294974665985995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66017164062863316443990663 99025746094294974665985995)
          ·
            refine ⟨148538619141442461998978993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99025746094294974665985995 148538619141442461998978993)
            ·
              refine ⟨111403964356081846499234245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148538619141442461998978993 111403964356081846499234245)
              ·
                refine ⟨20888243316765346218606421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111403964356081846499234245 20888243316765346218606421)
                ·
                  refine ⟨122392050684171950499647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20888243316765346218606421 122392050684171950499647)
                  ·
                    rfl

theorem cell23_2145219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 9].length) (baseStart_2145219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145219 prefixEnd_2145219 := by exact prefixLift 2145219
  have htrace : WordTrace (prefixWord ++ tailWord_2145219) baseStart_2145219 baseEnd_2145219 := by
    simpa [prefixWord, tailWord_2145219, baseEnd_2145219] using wordTrace_append hprefix tailTrace_2145219
  have hstable : (prefixWord ++ tailWord_2145219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145219).length < 2 ^ (prefixWord ++ tailWord_2145219).sum := by decide
  have hdescent : baseEnd_2145219 < baseStart_2145219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145226 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2145226 : Nat := 118140960795 + 2145226 * 2 ^ 59
def prefixEnd_2145226 : Nat := 4983230072969 + 3 ^ 40 * 2145226 * 2
def baseEnd_2145226 : Nat := 1101532050522129027109291

theorem tailTrace_2145226 : CollatzResearch.WordTrace tailWord_2145226 prefixEnd_2145226 1101532050522129027109291 := by
  unfold tailWord_2145226
  simp only [CollatzResearch.WordTrace]
  refine ⟨19560705031555013069317883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52161880084146701518181021 19560705031555013069317883)
  ·
    refine ⟨29341057547332519603976825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19560705031555013069317883 29341057547332519603976825)
    ·
      refine ⟨22005793160499389702982619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29341057547332519603976825 22005793160499389702982619)
      ·
        refine ⟨33008689740749084554473929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22005793160499389702982619 33008689740749084554473929)
        ·
          refine ⟨24756517305561813415855447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33008689740749084554473929 24756517305561813415855447)
          ·
            refine ⟨37134775958342720123783171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24756517305561813415855447 37134775958342720123783171)
            ·
              refine ⟨55702163937514080185674757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37134775958342720123783171 55702163937514080185674757)
              ·
                refine ⟨10444155738283890034814017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55702163937514080185674757 10444155738283890034814017)
                ·
                  refine ⟨7833116803712917526110513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10444155738283890034814017 7833116803712917526110513)
                  ·
                    refine ⟨5874837602784688144582885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7833116803712917526110513 5874837602784688144582885)
                    ·
                      refine ⟨1101532050522129027109291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5874837602784688144582885 1101532050522129027109291)
                      ·
                        rfl

theorem cell23_2145226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2145226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145226 prefixEnd_2145226 := by exact prefixLift 2145226
  have htrace : WordTrace (prefixWord ++ tailWord_2145226) baseStart_2145226 baseEnd_2145226 := by
    simpa [prefixWord, tailWord_2145226, baseEnd_2145226] using wordTrace_append hprefix tailTrace_2145226
  have hstable : (prefixWord ++ tailWord_2145226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145226).length < 2 ^ (prefixWord ++ tailWord_2145226).sum := by decide
  have hdescent : baseEnd_2145226 < baseStart_2145226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145268 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2145268 : Nat := 118140960795 + 2145268 * 2 ^ 59
def prefixEnd_2145268 : Nat := 4983230072969 + 3 ^ 40 * 2145268 * 2
def baseEnd_2145268 : Nat := 1101553616709617862784099

theorem tailTrace_2145268 : CollatzResearch.WordTrace tailWord_2145268 prefixEnd_2145268 1101553616709617862784099 := by
  unfold tailWord_2145268
  simp only [CollatzResearch.WordTrace]
  refine ⟨39122175996033946725150229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52162901328045262300200305 39122175996033946725150229)
  ·
    refine ⟨1833851999814091252741417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39122175996033946725150229 1833851999814091252741417)
    ·
      refine ⟨1375388999860568439556063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1833851999814091252741417 1375388999860568439556063)
      ·
        refine ⟨2063083499790852659334095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375388999860568439556063 2063083499790852659334095)
        ·
          refine ⟨3094625249686278989001143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063083499790852659334095 3094625249686278989001143)
          ·
            refine ⟨4641937874529418483501715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094625249686278989001143 4641937874529418483501715)
            ·
              refine ⟨6962906811794127725252573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4641937874529418483501715 6962906811794127725252573)
              ·
                refine ⟨2611090054422797896969715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6962906811794127725252573 2611090054422797896969715)
                ·
                  refine ⟨3916635081634196845454573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611090054422797896969715 3916635081634196845454573)
                  ·
                    refine ⟨1468738155612823817045465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3916635081634196845454573 1468738155612823817045465)
                    ·
                      refine ⟨1101553616709617862784099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468738155612823817045465 1101553616709617862784099)
                      ·
                        rfl

theorem cell23_2145268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2145268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145268 prefixEnd_2145268 := by exact prefixLift 2145268
  have htrace : WordTrace (prefixWord ++ tailWord_2145268) baseStart_2145268 baseEnd_2145268 := by
    simpa [prefixWord, tailWord_2145268, baseEnd_2145268] using wordTrace_append hprefix tailTrace_2145268
  have hstable : (prefixWord ++ tailWord_2145268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145268).length < 2 ^ (prefixWord ++ tailWord_2145268).sum := by decide
  have hdescent : baseEnd_2145268 < baseStart_2145268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145270 : List Nat := [5, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_2145270 : Nat := 118140960795 + 2145270 * 2 ^ 59
def prefixEnd_2145270 : Nat := 4983230072969 + 3 ^ 40 * 2145270 * 2
def baseEnd_2145270 : Nat := 122394960407880761662121

theorem tailTrace_2145270 : CollatzResearch.WordTrace tailWord_2145270 prefixEnd_2145270 122394960407880761662121 := by
  unfold tailWord_2145270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4890276558628790486992079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52162949958707098527915509 4890276558628790486992079)
  ·
    refine ⟨7335414837943185730488119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4890276558628790486992079 7335414837943185730488119)
    ·
      refine ⟨11003122256914778595732179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7335414837943185730488119 11003122256914778595732179)
      ·
        refine ⟨16504683385372167893598269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11003122256914778595732179 16504683385372167893598269)
        ·
          refine ⟨6189256269514562960099351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16504683385372167893598269 6189256269514562960099351)
          ·
            refine ⟨9283884404271844440149027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189256269514562960099351 9283884404271844440149027)
            ·
              refine ⟨13925826606407766660223541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9283884404271844440149027 13925826606407766660223541)
              ·
                refine ⟨1305546244350728124395957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13925826606407766660223541 1305546244350728124395957)
                ·
                  refine ⟨122394960407880761662121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1305546244350728124395957 122394960407880761662121)
                  ·
                    rfl

theorem cell23_2145270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_2145270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145270 prefixEnd_2145270 := by exact prefixLift 2145270
  have htrace : WordTrace (prefixWord ++ tailWord_2145270) baseStart_2145270 baseEnd_2145270 := by
    simpa [prefixWord, tailWord_2145270, baseEnd_2145270] using wordTrace_append hprefix tailTrace_2145270
  have hstable : (prefixWord ++ tailWord_2145270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145270).length < 2 ^ (prefixWord ++ tailWord_2145270).sum := by decide
  have hdescent : baseEnd_2145270 < baseStart_2145270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145298 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2145298 : Nat := 118140960795 + 2145298 * 2 ^ 59
def prefixEnd_2145298 : Nat := 4983230072969 + 3 ^ 40 * 2145298 * 2
def baseEnd_2145298 : Nat := 1101569021129252745408961

theorem tailTrace_2145298 : CollatzResearch.WordTrace tailWord_2145298 prefixEnd_2145298 1101569021129252745408961 := by
  unfold tailWord_2145298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19561361545489802143473137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52163630787972805715928365 19561361545489802143473137)
  ·
    refine ⟨14671021159117351607604853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19561361545489802143473137 14671021159117351607604853)
    ·
      refine ⟨1375408233667251713212955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14671021159117351607604853 1375408233667251713212955)
      ·
        refine ⟨2063112350500877569819433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375408233667251713212955 2063112350500877569819433)
        ·
          refine ⟨1547334262875658177364575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063112350500877569819433 1547334262875658177364575)
          ·
            refine ⟨2321001394313487266046863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547334262875658177364575 2321001394313487266046863)
            ·
              refine ⟨3481502091470230899070295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321001394313487266046863 3481502091470230899070295)
              ·
                refine ⟨5222253137205346348605443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481502091470230899070295 5222253137205346348605443)
                ·
                  refine ⟨7833379705808019522908165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5222253137205346348605443 7833379705808019522908165)
                  ·
                    refine ⟨1468758694839003660545281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7833379705808019522908165 1468758694839003660545281)
                    ·
                      refine ⟨1101569021129252745408961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468758694839003660545281 1101569021129252745408961)
                      ·
                        rfl

theorem cell23_2145298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2145298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145298 prefixEnd_2145298 := by exact prefixLift 2145298
  have htrace : WordTrace (prefixWord ++ tailWord_2145298) baseStart_2145298 baseEnd_2145298 := by
    simpa [prefixWord, tailWord_2145298, baseEnd_2145298] using wordTrace_append hprefix tailTrace_2145298
  have hstable : (prefixWord ++ tailWord_2145298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145298).length < 2 ^ (prefixWord ++ tailWord_2145298).sum := by decide
  have hdescent : baseEnd_2145298 < baseStart_2145298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145303 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2145303 : Nat := 118140960795 + 2145303 * 2 ^ 59
def prefixEnd_2145303 : Nat := 4983230072969 + 3 ^ 40 * 2145303 * 2
def baseEnd_2145303 : Nat := 1101571588532525225846437

theorem tailTrace_2145303 : CollatzResearch.WordTrace tailWord_2145303 prefixEnd_2145303 1101571588532525225846437 := by
  unfold tailWord_2145303
  simp only [CollatzResearch.WordTrace]
  refine ⟨78245628546941094427824563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52163752364627396285216375 78245628546941094427824563)
  ·
    refine ⟨117368442820411641641736845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78245628546941094427824563 117368442820411641641736845)
    ·
      refine ⟨44013166057654365615651317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117368442820411641641736845 44013166057654365615651317)
      ·
        refine ⟨4126234317905096776467311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44013166057654365615651317 4126234317905096776467311)
        ·
          refine ⟨6189351476857645164700967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126234317905096776467311 6189351476857645164700967)
          ·
            refine ⟨9284027215286467747051451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189351476857645164700967 9284027215286467747051451)
            ·
              refine ⟨13926040822929701620577177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9284027215286467747051451 13926040822929701620577177)
              ·
                refine ⟨10444530617197276215432883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13926040822929701620577177 10444530617197276215432883)
                ·
                  refine ⟨15666795925795914323149325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10444530617197276215432883 15666795925795914323149325)
                  ·
                    refine ⟨5875048472173467871180997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15666795925795914323149325 5875048472173467871180997)
                    ·
                      refine ⟨1101571588532525225846437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5875048472173467871180997 1101571588532525225846437)
                      ·
                        rfl

theorem cell23_2145303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2145303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145303 prefixEnd_2145303 := by exact prefixLift 2145303
  have htrace : WordTrace (prefixWord ++ tailWord_2145303) baseStart_2145303 baseEnd_2145303 := by
    simpa [prefixWord, tailWord_2145303, baseEnd_2145303] using wordTrace_append hprefix tailTrace_2145303
  have hstable : (prefixWord ++ tailWord_2145303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145303).length < 2 ^ (prefixWord ++ tailWord_2145303).sum := by decide
  have hdescent : baseEnd_2145303 < baseStart_2145303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145323 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 3]
def baseStart_2145323 : Nat := 118140960795 + 2145323 * 2 ^ 59
def prefixEnd_2145323 : Nat := 4983230072969 + 3 ^ 40 * 2145323 * 2
def baseEnd_2145323 : Nat := 1101581858145615147596345

theorem tailTrace_2145323 : CollatzResearch.WordTrace tailWord_2145323 prefixEnd_2145323 1101581858145615147596345 := by
  unfold tailWord_2145323
  simp only [CollatzResearch.WordTrace]
  refine ⟨78246358006868637843552623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52164238671245758562368415 78246358006868637843552623)
  ·
    refine ⟨117369537010302956765328935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78246358006868637843552623 117369537010302956765328935)
    ·
      refine ⟨176054305515454435147993403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117369537010302956765328935 176054305515454435147993403)
      ·
        refine ⟨264081458273181652721990105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176054305515454435147993403 264081458273181652721990105)
        ·
          refine ⟨198061093704886239541492579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264081458273181652721990105 198061093704886239541492579)
          ·
            refine ⟨297091640557329359312238869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198061093704886239541492579 297091640557329359312238869)
            ·
              refine ⟨13926170651124813717761197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 297091640557329359312238869 13926170651124813717761197)
              ·
                refine ⟨5222313994171805144160449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13926170651124813717761197 5222313994171805144160449)
                ·
                  refine ⟨3916735495628853858120337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5222313994171805144160449 3916735495628853858120337)
                  ·
                    refine ⟨2937551621721640393590253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916735495628853858120337 2937551621721640393590253)
                    ·
                      refine ⟨1101581858145615147596345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2937551621721640393590253 1101581858145615147596345)
                      ·
                        rfl

theorem cell23_2145323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 3].length) (baseStart_2145323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145323 prefixEnd_2145323 := by exact prefixLift 2145323
  have htrace : WordTrace (prefixWord ++ tailWord_2145323) baseStart_2145323 baseEnd_2145323 := by
    simpa [prefixWord, tailWord_2145323, baseEnd_2145323] using wordTrace_append hprefix tailTrace_2145323
  have hstable : (prefixWord ++ tailWord_2145323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145323).length < 2 ^ (prefixWord ++ tailWord_2145323).sum := by decide
  have hdescent : baseEnd_2145323 < baseStart_2145323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145340 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_2145340 : Nat := 118140960795 + 2145340 * 2 ^ 59
def prefixEnd_2145340 : Nat := 4983230072969 + 3 ^ 40 * 2145340 * 2
def baseEnd_2145340 : Nat := 1101590587316741581083767

theorem tailTrace_2145340 : CollatzResearch.WordTrace tailWord_2145340 prefixEnd_2145340 1101590587316741581083767 := by
  unfold tailWord_2145340
  simp only [CollatzResearch.WordTrace]
  refine ⟨39123489023903524873460737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52164652031871366497947649 39123489023903524873460737)
  ·
    refine ⟨29342616767927643655095553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39123489023903524873460737 29342616767927643655095553)
    ·
      refine ⟨22006962575945732741321665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29342616767927643655095553 22006962575945732741321665)
      ·
        refine ⟨16505221931959299555991249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22006962575945732741321665 16505221931959299555991249)
        ·
          refine ⟨12378916448969474666993437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16505221931959299555991249 12378916448969474666993437)
          ·
            refine ⟨4642093668363553000122539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12378916448969474666993437 4642093668363553000122539)
            ·
              refine ⟨6963140502545329500183809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642093668363553000122539 6963140502545329500183809)
              ·
                refine ⟨5222355376908997125137857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6963140502545329500183809 5222355376908997125137857)
                ·
                  refine ⟨3916766532681747843853393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5222355376908997125137857 3916766532681747843853393)
                  ·
                    refine ⟨2937574899511310882890045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916766532681747843853393 2937574899511310882890045)
                    ·
                      refine ⟨1101590587316741581083767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2937574899511310882890045 1101590587316741581083767)
                      ·
                        rfl

theorem cell23_2145340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_2145340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145340 prefixEnd_2145340 := by exact prefixLift 2145340
  have htrace : WordTrace (prefixWord ++ tailWord_2145340) baseStart_2145340 baseEnd_2145340 := by
    simpa [prefixWord, tailWord_2145340, baseEnd_2145340] using wordTrace_append hprefix tailTrace_2145340
  have hstable : (prefixWord ++ tailWord_2145340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145340).length < 2 ^ (prefixWord ++ tailWord_2145340).sum := by decide
  have hdescent : baseEnd_2145340 < baseStart_2145340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145347 : List Nat := [1, 1, 1, 3, 1, 2, 7, 2, 1, 4]
def baseStart_2145347 : Nat := 118140960795 + 2145347 * 2 ^ 59
def prefixEnd_2145347 : Nat := 4983230072969 + 3 ^ 40 * 2145347 * 2
def baseEnd_2145347 : Nat := 367198060560441017898745

theorem tailTrace_2145347 : CollatzResearch.WordTrace tailWord_2145347 prefixEnd_2145347 367198060560441017898745 := by
  unfold tailWord_2145347
  simp only [CollatzResearch.WordTrace]
  refine ⟨78247233358781689942426295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52164822239187793294950863 78247233358781689942426295)
  ·
    refine ⟨117370850038172534913639443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78247233358781689942426295 117370850038172534913639443)
    ·
      refine ⟨176056275057258802370459165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117370850038172534913639443 176056275057258802370459165)
      ·
        refine ⟨66021103146472050888922187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176056275057258802370459165 66021103146472050888922187)
        ·
          refine ⟨99031654719708076333383281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66021103146472050888922187 99031654719708076333383281)
          ·
            refine ⟨74273741039781057250037461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99031654719708076333383281 74273741039781057250037461)
            ·
              refine ⟨1740790805619868529297753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74273741039781057250037461 1740790805619868529297753)
              ·
                refine ⟨1305593104214901396973315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740790805619868529297753 1305593104214901396973315)
                ·
                  refine ⟨1958389656322352095459973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305593104214901396973315 1958389656322352095459973)
                  ·
                    refine ⟨367198060560441017898745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958389656322352095459973 367198060560441017898745)
                    ·
                      rfl

theorem cell23_2145347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 1, 4].length) (baseStart_2145347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145347 prefixEnd_2145347 := by exact prefixLift 2145347
  have htrace : WordTrace (prefixWord ++ tailWord_2145347) baseStart_2145347 baseEnd_2145347 := by
    simpa [prefixWord, tailWord_2145347, baseEnd_2145347] using wordTrace_append hprefix tailTrace_2145347
  have hstable : (prefixWord ++ tailWord_2145347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145347).length < 2 ^ (prefixWord ++ tailWord_2145347).sum := by decide
  have hdescent : baseEnd_2145347 < baseStart_2145347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145356 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_2145356 : Nat := 118140960795 + 2145356 * 2 ^ 59
def prefixEnd_2145356 : Nat := 4983230072969 + 3 ^ 40 * 2145356 * 2
def baseEnd_2145356 : Nat := 367199601002404506161231

theorem tailTrace_2145356 : CollatzResearch.WordTrace tailWord_2145356 prefixEnd_2145356 367199601002404506161231 := by
  unfold tailWord_2145356
  simp only [CollatzResearch.WordTrace]
  refine ⟨39123780807874542239751961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52165041077166056319669281 39123780807874542239751961)
  ·
    refine ⟨29342835605905906679813971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39123780807874542239751961 29342835605905906679813971)
    ·
      refine ⟨44014253408858860019720957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29342835605905906679813971 44014253408858860019720957)
      ·
        refine ⟨16505345028322072507395359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44014253408858860019720957 16505345028322072507395359)
        ·
          refine ⟨24758017542483108761093039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16505345028322072507395359 24758017542483108761093039)
          ·
            refine ⟨37137026313724663141639559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24758017542483108761093039 37137026313724663141639559)
            ·
              refine ⟨55705539470586994712459339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37137026313724663141639559 55705539470586994712459339)
              ·
                refine ⟨83558309205880492068689009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55705539470586994712459339 83558309205880492068689009)
                ·
                  refine ⟨62668731904410369051516757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83558309205880492068689009 62668731904410369051516757)
                  ·
                    refine ⟨367199601002404506161231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 62668731904410369051516757 367199601002404506161231)
                    ·
                      rfl

theorem cell23_2145356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_2145356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145356 prefixEnd_2145356 := by exact prefixLift 2145356
  have htrace : WordTrace (prefixWord ++ tailWord_2145356) baseStart_2145356 baseEnd_2145356 := by
    simpa [prefixWord, tailWord_2145356, baseEnd_2145356] using wordTrace_append hprefix tailTrace_2145356
  have hstable : (prefixWord ++ tailWord_2145356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145356).length < 2 ^ (prefixWord ++ tailWord_2145356).sum := by decide
  have hdescent : baseEnd_2145356 < baseStart_2145356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145374 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2145374 : Nat := 118140960795 + 2145374 * 2 ^ 59
def prefixEnd_2145374 : Nat := 4983230072969 + 3 ^ 40 * 2145374 * 2
def baseEnd_2145374 : Nat := 1101608045658994448058611

theorem tailTrace_2145374 : CollatzResearch.WordTrace tailWord_2145374 prefixEnd_2145374 1101608045658994448058611 := by
  unfold tailWord_2145374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9781027266210484194207397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52165478753122582369106117 9781027266210484194207397)
  ·
    refine ⟨1833942612414465786413887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9781027266210484194207397 1833942612414465786413887)
    ·
      refine ⟨2750913918621698679620831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1833942612414465786413887 2750913918621698679620831)
      ·
        refine ⟨4126370877932548019431247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2750913918621698679620831 4126370877932548019431247)
        ·
          refine ⟨6189556316898822029146871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126370877932548019431247 6189556316898822029146871)
          ·
            refine ⟨9284334475348233043720307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189556316898822029146871 9284334475348233043720307)
            ·
              refine ⟨13926501713022349565580461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9284334475348233043720307 13926501713022349565580461)
              ·
                refine ⟨5222438142383381087092673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13926501713022349565580461 5222438142383381087092673)
                ·
                  refine ⟨3916828606787535815319505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5222438142383381087092673 3916828606787535815319505)
                  ·
                    refine ⟨2937621455090651861489629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3916828606787535815319505 2937621455090651861489629)
                    ·
                      refine ⟨1101608045658994448058611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2937621455090651861489629 1101608045658994448058611)
                      ·
                        rfl

theorem cell23_2145374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2145374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145374 prefixEnd_2145374 := by exact prefixLift 2145374
  have htrace : WordTrace (prefixWord ++ tailWord_2145374) baseStart_2145374 baseEnd_2145374 := by
    simpa [prefixWord, tailWord_2145374, baseEnd_2145374] using wordTrace_append hprefix tailTrace_2145374
  have hstable : (prefixWord ++ tailWord_2145374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145374).length < 2 ^ (prefixWord ++ tailWord_2145374).sum := by decide
  have hdescent : baseEnd_2145374 < baseStart_2145374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145403 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 4, 4]
def baseStart_2145403 : Nat := 118140960795 + 2145403 * 2 ^ 59
def prefixEnd_2145403 : Nat := 4983230072969 + 3 ^ 40 * 2145403 * 2
def baseEnd_2145403 : Nat := 367207645532658278198659

theorem tailTrace_2145403 : CollatzResearch.WordTrace tailWord_2145403 prefixEnd_2145403 367207645532658278198659 := by
  unfold tailWord_2145403
  simp only [CollatzResearch.WordTrace]
  refine ⟨78249275846578811506464863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52166183897719207670976575 78249275846578811506464863)
  ·
    refine ⟨117373913769868217259697295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78249275846578811506464863 117373913769868217259697295)
    ·
      refine ⟨176060870654802325889545943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117373913769868217259697295 176060870654802325889545943)
      ·
        refine ⟨264091305982203488834318915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176060870654802325889545943 264091305982203488834318915)
        ·
          refine ⟨396136958973305233251478373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264091305982203488834318915 396136958973305233251478373)
          ·
            refine ⟨74275679807494731234652195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 396136958973305233251478373 74275679807494731234652195)
            ·
              refine ⟨111413519711242096851978293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74275679807494731234652195 111413519711242096851978293)
              ·
                refine ⟨10445017472928946579872965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111413519711242096851978293 10445017472928946579872965)
                ·
                  refine ⟨1958440776174177483726181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10445017472928946579872965 1958440776174177483726181)
                  ·
                    refine ⟨367207645532658278198659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958440776174177483726181 367207645532658278198659)
                    ·
                      rfl

theorem cell23_2145403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 4].length) (baseStart_2145403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145403 prefixEnd_2145403 := by exact prefixLift 2145403
  have htrace : WordTrace (prefixWord ++ tailWord_2145403) baseStart_2145403 baseEnd_2145403 := by
    simpa [prefixWord, tailWord_2145403, baseEnd_2145403] using wordTrace_append hprefix tailTrace_2145403
  have hstable : (prefixWord ++ tailWord_2145403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145403).length < 2 ^ (prefixWord ++ tailWord_2145403).sum := by decide
  have hdescent : baseEnd_2145403 < baseStart_2145403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145444 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_2145444 : Nat := 118140960795 + 2145444 * 2 ^ 59
def prefixEnd_2145444 : Nat := 4983230072969 + 3 ^ 40 * 2145444 * 2
def baseEnd_2145444 : Nat := 1101643989304809174183289

theorem tailTrace_2145444 : CollatzResearch.WordTrace tailWord_2145444 prefixEnd_2145444 1101643989304809174183289 := by
  unfold tailWord_2145444
  simp only [CollatzResearch.WordTrace]
  refine ⟨39125385619715137754353693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52167180826286850339138257 39125385619715137754353693)
  ·
    refine ⟨14672019607393176657882635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39125385619715137754353693 14672019607393176657882635)
    ·
      refine ⟨22008029411089764986823953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14672019607393176657882635 22008029411089764986823953)
      ·
        refine ⟨16506022058317323740117965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22008029411089764986823953 16506022058317323740117965)
        ·
          refine ⟨6189758271868996402544237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16506022058317323740117965 6189758271868996402544237)
          ·
            refine ⟨2321159351950873650954089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6189758271868996402544237 2321159351950873650954089)
            ·
              refine ⟨1740869513963155238215567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2321159351950873650954089 1740869513963155238215567)
              ·
                refine ⟨2611304270944732857323351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740869513963155238215567 2611304270944732857323351)
                ·
                  refine ⟨3916956406417099285985027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611304270944732857323351 3916956406417099285985027)
                  ·
                    refine ⟨5875434609625648928977541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3916956406417099285985027 5875434609625648928977541)
                    ·
                      refine ⟨1101643989304809174183289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5875434609625648928977541 1101643989304809174183289)
                      ·
                        rfl

theorem cell23_2145444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_2145444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145444 prefixEnd_2145444 := by exact prefixLift 2145444
  have htrace : WordTrace (prefixWord ++ tailWord_2145444) baseStart_2145444 baseEnd_2145444 := by
    simpa [prefixWord, tailWord_2145444, baseEnd_2145444] using wordTrace_append hprefix tailTrace_2145444
  have hstable : (prefixWord ++ tailWord_2145444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145444).length < 2 ^ (prefixWord ++ tailWord_2145444).sum := by decide
  have hdescent : baseEnd_2145444 < baseStart_2145444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145450 : List Nat := [3, 1, 5, 1, 1, 2, 10]
def baseStart_2145450 : Nat := 118140960795 + 2145450 * 2 ^ 59
def prefixEnd_2145450 : Nat := 4983230072969 + 3 ^ 40 * 2145450 * 2
def baseEnd_2145450 : Nat := 13600581113441187045781

theorem tailTrace_2145450 : CollatzResearch.WordTrace tailWord_2145450 prefixEnd_2145450 13600581113441187045781 := by
  unfold tailWord_2145450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19562747519352134633356451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52167326718272359022283869 19562747519352134633356451)
  ·
    refine ⟨29344121279028201950034677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19562747519352134633356451 29344121279028201950034677)
    ·
      refine ⟨2751011369908893932815751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29344121279028201950034677 2751011369908893932815751)
      ·
        refine ⟨4126517054863340899223627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751011369908893932815751 4126517054863340899223627)
        ·
          refine ⟨6189775582295011348835441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126517054863340899223627 6189775582295011348835441)
          ·
            refine ⟨4642331686721258511626581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6189775582295011348835441 4642331686721258511626581)
            ·
              refine ⟨13600581113441187045781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4642331686721258511626581 13600581113441187045781)
              ·
                rfl

theorem cell23_2145450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 10].length) (baseStart_2145450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145450 prefixEnd_2145450 := by exact prefixLift 2145450
  have htrace : WordTrace (prefixWord ++ tailWord_2145450) baseStart_2145450 baseEnd_2145450 := by
    simpa [prefixWord, tailWord_2145450, baseEnd_2145450] using wordTrace_append hprefix tailTrace_2145450
  have hstable : (prefixWord ++ tailWord_2145450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145450).length < 2 ^ (prefixWord ++ tailWord_2145450).sum := by decide
  have hdescent : baseEnd_2145450 < baseStart_2145450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145474 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2145474 : Nat := 118140960795 + 2145474 * 2 ^ 59
def prefixEnd_2145474 : Nat := 4983230072969 + 3 ^ 40 * 2145474 * 2
def baseEnd_2145474 : Nat := 1101659393724444056808151

theorem tailTrace_2145474 : CollatzResearch.WordTrace tailWord_2145474 prefixEnd_2145474 1101659393724444056808151 := by
  unfold tailWord_2145474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19562966357330397658074869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52167910286214393754866317 19562966357330397658074869)
  ·
    refine ⟨1834028095999724780444519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19562966357330397658074869 1834028095999724780444519)
    ·
      refine ⟨2751042143999587170666779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1834028095999724780444519 2751042143999587170666779)
      ·
        refine ⟨4126563215999380756000169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751042143999587170666779 4126563215999380756000169)
        ·
          refine ⟨3094922411999535567000127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4126563215999380756000169 3094922411999535567000127)
          ·
            refine ⟨4642383617999303350500191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094922411999535567000127 4642383617999303350500191)
            ·
              refine ⟨6963575426998955025750287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642383617999303350500191 6963575426998955025750287)
              ·
                refine ⟨10445363140498432538625431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6963575426998955025750287 10445363140498432538625431)
                ·
                  refine ⟨15668044710747648807938147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10445363140498432538625431 15668044710747648807938147)
                  ·
                    refine ⟨23502067066121473211907221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15668044710747648807938147 23502067066121473211907221)
                    ·
                      refine ⟨1101659393724444056808151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23502067066121473211907221 1101659393724444056808151)
                      ·
                        rfl

theorem cell23_2145474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2145474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145474 prefixEnd_2145474 := by exact prefixLift 2145474
  have htrace : WordTrace (prefixWord ++ tailWord_2145474) baseStart_2145474 baseEnd_2145474 := by
    simpa [prefixWord, tailWord_2145474, baseEnd_2145474] using wordTrace_append hprefix tailTrace_2145474
  have hstable : (prefixWord ++ tailWord_2145474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145474).length < 2 ^ (prefixWord ++ tailWord_2145474).sum := by decide
  have hdescent : baseEnd_2145474 < baseStart_2145474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145478 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2145478 : Nat := 118140960795 + 2145478 * 2 ^ 59
def prefixEnd_2145478 : Nat := 4983230072969 + 3 ^ 40 * 2145478 * 2
def baseEnd_2145478 : Nat := 1101661447647062041158133

theorem tailTrace_2145478 : CollatzResearch.WordTrace tailWord_2145478 prefixEnd_2145478 1101661447647062041158133 := by
  unfold tailWord_2145478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445375353790846853607659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52168007547538066210296725 2445375353790846853607659)
  ·
    refine ⟨3668063030686270280411489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2445375353790846853607659 3668063030686270280411489)
    ·
      refine ⟨2751047273014702710308617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3668063030686270280411489 2751047273014702710308617)
      ·
        refine ⟨2063285454761027032731463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2751047273014702710308617 2063285454761027032731463)
        ·
          refine ⟨3094928182141540549097195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063285454761027032731463 3094928182141540549097195)
          ·
            refine ⟨4642392273212310823645793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094928182141540549097195 4642392273212310823645793)
            ·
              refine ⟨3481794204909233117734345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4642392273212310823645793 3481794204909233117734345)
              ·
                refine ⟨2611345653681924838300759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481794204909233117734345 2611345653681924838300759)
                ·
                  refine ⟨3917018480522887257451139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611345653681924838300759 3917018480522887257451139)
                  ·
                    refine ⟨5875527720784330886176709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3917018480522887257451139 5875527720784330886176709)
                    ·
                      refine ⟨1101661447647062041158133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5875527720784330886176709 1101661447647062041158133)
                      ·
                        rfl

theorem cell23_2145478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2145478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145478 prefixEnd_2145478 := by exact prefixLift 2145478
  have htrace : WordTrace (prefixWord ++ tailWord_2145478) baseStart_2145478 baseEnd_2145478 := by
    simpa [prefixWord, tailWord_2145478, baseEnd_2145478] using wordTrace_append hprefix tailTrace_2145478
  have hstable : (prefixWord ++ tailWord_2145478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145478).length < 2 ^ (prefixWord ++ tailWord_2145478).sum := by decide
  have hdescent : baseEnd_2145478 < baseStart_2145478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145503 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2145503 : Nat := 118140960795 + 2145503 * 2 ^ 59
def prefixEnd_2145503 : Nat := 4983230072969 + 3 ^ 40 * 2145503 * 2
def baseEnd_2145503 : Nat := 1101674284663424443345517

theorem tailTrace_2145503 : CollatzResearch.WordTrace tailWord_2145503 prefixEnd_2145503 1101674284663424443345517 := by
  unfold tailWord_2145503
  simp only [CollatzResearch.WordTrace]
  refine ⟨78252923146216528585105163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52168615430811019056736775 78252923146216528585105163)
  ·
    refine ⟨117379384719324792877657745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78252923146216528585105163 117379384719324792877657745)
    ·
      refine ⟨88034538539493594658243309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117379384719324792877657745 88034538539493594658243309)
      ·
        refine ⟨33012951952310097996841241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88034538539493594658243309 33012951952310097996841241)
        ·
          refine ⟨24759713964232573497630931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33012951952310097996841241 24759713964232573497630931)
          ·
            refine ⟨37139570946348860246446397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24759713964232573497630931 37139570946348860246446397)
            ·
              refine ⟨13927339104880822592417399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37139570946348860246446397 13927339104880822592417399)
              ·
                refine ⟨20891008657321233888626099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13927339104880822592417399 20891008657321233888626099)
                ·
                  refine ⟨31336512985981850832939149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20891008657321233888626099 31336512985981850832939149)
                  ·
                    refine ⟨11751192369743194062352181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31336512985981850832939149 11751192369743194062352181)
                    ·
                      refine ⟨1101674284663424443345517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11751192369743194062352181 1101674284663424443345517)
                      ·
                        rfl

theorem cell23_2145503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2145503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145503 prefixEnd_2145503 := by exact prefixLift 2145503
  have htrace : WordTrace (prefixWord ++ tailWord_2145503) baseStart_2145503 baseEnd_2145503 := by
    simpa [prefixWord, tailWord_2145503, baseEnd_2145503] using wordTrace_append hprefix tailTrace_2145503
  have hstable : (prefixWord ++ tailWord_2145503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145503).length < 2 ^ (prefixWord ++ tailWord_2145503).sum := by decide
  have hdescent : baseEnd_2145503 < baseStart_2145503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145538 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2145538 : Nat := 118140960795 + 2145538 * 2 ^ 59
def prefixEnd_2145538 : Nat := 4983230072969 + 3 ^ 40 * 2145538 * 2
def baseEnd_2145538 : Nat := 1101692256486331806407857

theorem tailTrace_2145538 : CollatzResearch.WordTrace tailWord_2145538 prefixEnd_2145538 1101692256486331806407857 := by
  unfold tailWord_2145538
  simp only [CollatzResearch.WordTrace]
  refine ⟨19563549925272432390657317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52169466467393153041752845 19563549925272432390657317)
  ·
    refine ⟨3668165610988581073248247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19563549925272432390657317 3668165610988581073248247)
    ·
      refine ⟨5502248416482871609872371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3668165610988581073248247 5502248416482871609872371)
      ·
        refine ⟨8253372624724307414808557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5502248416482871609872371 8253372624724307414808557)
        ·
          refine ⟨3095014734271615280553209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8253372624724307414808557 3095014734271615280553209)
          ·
            refine ⟨2321261050703711460414907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3095014734271615280553209 2321261050703711460414907)
            ·
              refine ⟨3481891576055567190622361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321261050703711460414907 3481891576055567190622361)
              ·
                refine ⟨2611418682041675392966771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3481891576055567190622361 2611418682041675392966771)
                ·
                  refine ⟨3917128023062513089450157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611418682041675392966771 3917128023062513089450157)
                  ·
                    refine ⟨1468923008648442408543809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3917128023062513089450157 1468923008648442408543809)
                    ·
                      refine ⟨1101692256486331806407857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1468923008648442408543809 1101692256486331806407857)
                      ·
                        rfl

theorem cell23_2145538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2145538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145538 prefixEnd_2145538 := by exact prefixLift 2145538
  have htrace : WordTrace (prefixWord ++ tailWord_2145538) baseStart_2145538 baseEnd_2145538 := by
    simpa [prefixWord, tailWord_2145538, baseEnd_2145538] using wordTrace_append hprefix tailTrace_2145538
  have hstable : (prefixWord ++ tailWord_2145538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145538).length < 2 ^ (prefixWord ++ tailWord_2145538).sum := by decide
  have hdescent : baseEnd_2145538 < baseStart_2145538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145583 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 2, 8]
def baseStart_2145583 : Nat := 118140960795 + 2145583 * 2 ^ 59
def prefixEnd_2145583 : Nat := 4983230072969 + 3 ^ 40 * 2145583 * 2
def baseEnd_2145583 : Nat := 367238454371928043448383

theorem tailTrace_2145583 : CollatzResearch.WordTrace tailWord_2145583 prefixEnd_2145583 367238454371928043448383 := by
  unfold tailWord_2145583
  simp only [CollatzResearch.WordTrace]
  refine ⟨78255840985926702248017403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52170560657284468165344935 78255840985926702248017403)
  ·
    refine ⟨117383761478890053372026105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78255840985926702248017403 117383761478890053372026105)
    ·
      refine ⟨88037821109167540029019579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117383761478890053372026105 88037821109167540029019579)
      ·
        refine ⟨132056731663751310043529369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88037821109167540029019579 132056731663751310043529369)
        ·
          refine ⟨99042548747813482532647027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132056731663751310043529369 99042548747813482532647027)
          ·
            refine ⟨148563823121720223798970541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99042548747813482532647027 148563823121720223798970541)
            ·
              refine ⟨55711433670645083924613953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148563823121720223798970541 55711433670645083924613953)
              ·
                refine ⟨41783575252983812943460465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55711433670645083924613953 41783575252983812943460465)
                ·
                  refine ⟨31337681439737859707595349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41783575252983812943460465 31337681439737859707595349)
                  ·
                    refine ⟨367238454371928043448383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31337681439737859707595349 367238454371928043448383)
                    ·
                      rfl

theorem cell23_2145583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_2145583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145583 prefixEnd_2145583 := by exact prefixLift 2145583
  have htrace : WordTrace (prefixWord ++ tailWord_2145583) baseStart_2145583 baseEnd_2145583 := by
    simpa [prefixWord, tailWord_2145583, baseEnd_2145583] using wordTrace_append hprefix tailTrace_2145583
  have hstable : (prefixWord ++ tailWord_2145583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145583).length < 2 ^ (prefixWord ++ tailWord_2145583).sum := by decide
  have hdescent : baseEnd_2145583 < baseStart_2145583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145604 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2145604 : Nat := 118140960795 + 2145604 * 2 ^ 59
def prefixEnd_2145604 : Nat := 4983230072969 + 3 ^ 40 * 2145604 * 2
def baseEnd_2145604 : Nat := 367242048736509516060851

theorem tailTrace_2145604 : CollatzResearch.WordTrace tailWord_2145604 prefixEnd_2145604 367242048736509516060851 := by
  unfold tailWord_2145604
  simp only [CollatzResearch.WordTrace]
  refine ⟨39128303459425311417265933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52171071279233748556354577 39128303459425311417265933)
  ·
    refine ⟨14673113797284491781474725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39128303459425311417265933 14673113797284491781474725)
    ·
      refine ⟨2751208836990842209026511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14673113797284491781474725 2751208836990842209026511)
      ·
        refine ⟨4126813255486263313539767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751208836990842209026511 4126813255486263313539767)
        ·
          refine ⟨6190219883229394970309651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126813255486263313539767 6190219883229394970309651)
          ·
            refine ⟨9285329824844092455464477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6190219883229394970309651 9285329824844092455464477)
            ·
              refine ⟨3481998684316534670799179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9285329824844092455464477 3481998684316534670799179)
              ·
                refine ⟨5222998026474802006198769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3481998684316534670799179 5222998026474802006198769)
                ·
                  refine ⟨3917248519856101504649077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5222998026474802006198769 3917248519856101504649077)
                  ·
                    refine ⟨367242048736509516060851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3917248519856101504649077 367242048736509516060851)
                    ·
                      rfl

theorem cell23_2145604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2145604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145604 prefixEnd_2145604 := by exact prefixLift 2145604
  have htrace : WordTrace (prefixWord ++ tailWord_2145604) baseStart_2145604 baseEnd_2145604 := by
    simpa [prefixWord, tailWord_2145604, baseEnd_2145604] using wordTrace_append hprefix tailTrace_2145604
  have hstable : (prefixWord ++ tailWord_2145604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145604).length < 2 ^ (prefixWord ++ tailWord_2145604).sum := by decide
  have hdescent : baseEnd_2145604 < baseStart_2145604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145607 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_2145607 : Nat := 118140960795 + 2145607 * 2 ^ 59
def prefixEnd_2145607 : Nat := 4983230072969 + 3 ^ 40 * 2145607 * 2
def baseEnd_2145607 : Nat := 1101727686651492036445039

theorem tailTrace_2145607 : CollatzResearch.WordTrace tailWord_2145607 prefixEnd_2145607 1101727686651492036445039 := by
  unfold tailWord_2145607
  simp only [CollatzResearch.WordTrace]
  refine ⟨78256716337839754346891075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52171144225226502897927383 78256716337839754346891075)
  ·
    refine ⟨117385074506759631520336613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78256716337839754346891075 117385074506759631520336613)
    ·
      refine ⟨22009701470017430910063115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117385074506759631520336613 22009701470017430910063115)
      ·
        refine ⟨33014552205026146365094673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22009701470017430910063115 33014552205026146365094673)
        ·
          refine ⟨24760914153769609773821005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33014552205026146365094673 24760914153769609773821005)
          ·
            refine ⟨9285342807663603665182877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24760914153769609773821005 9285342807663603665182877)
            ·
              refine ⟨3482003552873851374443579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9285342807663603665182877 3482003552873851374443579)
              ·
                refine ⟨5223005329310777061665369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482003552873851374443579 5223005329310777061665369)
                ·
                  refine ⟨3917253996983082796249027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5223005329310777061665369 3917253996983082796249027)
                  ·
                    refine ⟨5875880995474624194373541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3917253996983082796249027 5875880995474624194373541)
                    ·
                      refine ⟨1101727686651492036445039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5875880995474624194373541 1101727686651492036445039)
                      ·
                        rfl

theorem cell23_2145607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_2145607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145607 prefixEnd_2145607 := by exact prefixLift 2145607
  have htrace : WordTrace (prefixWord ++ tailWord_2145607) baseStart_2145607 baseEnd_2145607 := by
    simpa [prefixWord, tailWord_2145607, baseEnd_2145607] using wordTrace_append hprefix tailTrace_2145607
  have hstable : (prefixWord ++ tailWord_2145607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145607).length < 2 ^ (prefixWord ++ tailWord_2145607).sum := by decide
  have hdescent : baseEnd_2145607 < baseStart_2145607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145620 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2145620 : Nat := 118140960795 + 2145620 * 2 ^ 59
def prefixEnd_2145620 : Nat := 4983230072969 + 3 ^ 40 * 2145620 * 2
def baseEnd_2145620 : Nat := 1101734361900000485582479

theorem tailTrace_2145620 : CollatzResearch.WordTrace tailWord_2145620 prefixEnd_2145620 1101734361900000485582479 := by
  unfold tailWord_2145620
  simp only [CollatzResearch.WordTrace]
  refine ⟨39128595243396328783557157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52171460324528438378076209 39128595243396328783557157)
  ·
    refine ⟨7336611608136811646916967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39128595243396328783557157 7336611608136811646916967)
    ·
      refine ⟨11004917412205217470375451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7336611608136811646916967 11004917412205217470375451)
      ·
        refine ⟨16507376118307826205563177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11004917412205217470375451 16507376118307826205563177)
        ·
          refine ⟨12380532088730869654172383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16507376118307826205563177 12380532088730869654172383)
          ·
            refine ⟨18570798133096304481258575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12380532088730869654172383 18570798133096304481258575)
            ·
              refine ⟨27856197199644456721887863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18570798133096304481258575 27856197199644456721887863)
              ·
                refine ⟨41784295799466685082831795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27856197199644456721887863 41784295799466685082831795)
                ·
                  refine ⟨62676443699200027624247693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41784295799466685082831795 62676443699200027624247693)
                  ·
                    refine ⟨23503666387200010359092885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62676443699200027624247693 23503666387200010359092885)
                    ·
                      refine ⟨1101734361900000485582479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23503666387200010359092885 1101734361900000485582479)
                      ·
                        rfl

theorem cell23_2145620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2145620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145620 prefixEnd_2145620 := by exact prefixLift 2145620
  have htrace : WordTrace (prefixWord ++ tailWord_2145620) baseStart_2145620 baseEnd_2145620 := by
    simpa [prefixWord, tailWord_2145620, baseEnd_2145620] using wordTrace_append hprefix tailTrace_2145620
  have hstable : (prefixWord ++ tailWord_2145620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145620).length < 2 ^ (prefixWord ++ tailWord_2145620).sum := by decide
  have hdescent : baseEnd_2145620 < baseStart_2145620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145634 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2145634 : Nat := 118140960795 + 2145634 * 2 ^ 59
def prefixEnd_2145634 : Nat := 4983230072969 + 3 ^ 40 * 2145634 * 2
def baseEnd_2145634 : Nat := 367247183543054476935805

theorem tailTrace_2145634 : CollatzResearch.WordTrace tailWord_2145634 prefixEnd_2145634 367247183543054476935805 := by
  unfold tailWord_2145634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19564425277185484489530989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52171800739161291972082637 19564425277185484489530989)
  ·
    refine ⟨7336659478944556683574121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19564425277185484489530989 7336659478944556683574121)
    ·
      refine ⟨5502494609208417512680591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7336659478944556683574121 5502494609208417512680591)
      ·
        refine ⟨8253741913812626269020887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5502494609208417512680591 8253741913812626269020887)
        ·
          refine ⟨12380612870718939403531331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8253741913812626269020887 12380612870718939403531331)
          ·
            refine ⟨18570919306078409105296997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12380612870718939403531331 18570919306078409105296997)
            ·
              refine ⟨3482047369889701707243187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18570919306078409105296997 3482047369889701707243187)
              ·
                refine ⟨5223071054834552560864781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482047369889701707243187 5223071054834552560864781)
                ·
                  refine ⟨1958651645562957210324293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5223071054834552560864781 1958651645562957210324293)
                  ·
                    refine ⟨367247183543054476935805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958651645562957210324293 367247183543054476935805)
                    ·
                      rfl

theorem cell23_2145634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2145634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145634 prefixEnd_2145634 := by exact prefixLift 2145634
  have htrace : WordTrace (prefixWord ++ tailWord_2145634) baseStart_2145634 baseEnd_2145634 := by
    simpa [prefixWord, tailWord_2145634, baseEnd_2145634] using wordTrace_append hprefix tailTrace_2145634
  have hstable : (prefixWord ++ tailWord_2145634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145634).length < 2 ^ (prefixWord ++ tailWord_2145634).sum := by decide
  have hdescent : baseEnd_2145634 < baseStart_2145634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145647 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 6]
def baseStart_2145647 : Nat := 118140960795 + 2145647 * 2 ^ 59
def prefixEnd_2145647 : Nat := 4983230072969 + 3 ^ 40 * 2145647 * 2
def baseEnd_2145647 : Nat := 122416469541963542216095

theorem tailTrace_2145647 : CollatzResearch.WordTrace tailWord_2145647 prefixEnd_2145647 122416469541963542216095 := by
  unfold tailWord_2145647
  simp only [CollatzResearch.WordTrace]
  refine ⟨78258175257694841178347195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52172116838463227452231463 78258175257694841178347195)
  ·
    refine ⟨117387262886542261767520793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78258175257694841178347195 117387262886542261767520793)
    ·
      refine ⟨88040447164906696325640595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117387262886542261767520793 88040447164906696325640595)
      ·
        refine ⟨132060670747360044488460893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88040447164906696325640595 132060670747360044488460893)
        ·
          refine ⟨49522751530260016683172835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132060670747360044488460893 49522751530260016683172835)
          ·
            refine ⟨74284127295390025024759253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49522751530260016683172835 74284127295390025024759253)
            ·
              refine ⟨1741034233485703711517795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74284127295390025024759253 1741034233485703711517795)
              ·
                refine ⟨2611551350228555567276693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741034233485703711517795 2611551350228555567276693)
                ·
                  refine ⟨122416469541963542216095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2611551350228555567276693 122416469541963542216095)
                  ·
                    rfl

theorem cell23_2145647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 6].length) (baseStart_2145647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145647 prefixEnd_2145647 := by exact prefixLift 2145647
  have htrace : WordTrace (prefixWord ++ tailWord_2145647) baseStart_2145647 baseEnd_2145647 := by
    simpa [prefixWord, tailWord_2145647, baseEnd_2145647] using wordTrace_append hprefix tailTrace_2145647
  have hstable : (prefixWord ++ tailWord_2145647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145647).length < 2 ^ (prefixWord ++ tailWord_2145647).sum := by decide
  have hdescent : baseEnd_2145647 < baseStart_2145647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145650 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2145650 : Nat := 118140960795 + 2145650 * 2 ^ 59
def prefixEnd_2145650 : Nat := 4983230072969 + 3 ^ 40 * 2145650 * 2
def baseEnd_2145650 : Nat := 1101749766319635368207341

theorem tailTrace_2145650 : CollatzResearch.WordTrace tailWord_2145650 prefixEnd_2145650 1101749766319635368207341 := by
  unfold tailWord_2145650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19564571169170993172676601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52172189784455981793804269 19564571169170993172676601)
  ·
    refine ⟨14673428376878244879507451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19564571169170993172676601 14673428376878244879507451)
    ·
      refine ⟨22010142565317367319261177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14673428376878244879507451 22010142565317367319261177)
      ·
        refine ⟨16507606923988025489445883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22010142565317367319261177 16507606923988025489445883)
        ·
          refine ⟨24761410385982038234168825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16507606923988025489445883 24761410385982038234168825)
          ·
            refine ⟨18571057789486528675626619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24761410385982038234168825 18571057789486528675626619)
            ·
              refine ⟨27856586684229793013439929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18571057789486528675626619 27856586684229793013439929)
              ·
                refine ⟨20892440013172344760079947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27856586684229793013439929 20892440013172344760079947)
                ·
                  refine ⟨31338660019758517140119921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20892440013172344760079947 31338660019758517140119921)
                  ·
                    refine ⟨23503995014818887855089941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31338660019758517140119921 23503995014818887855089941)
                    ·
                      refine ⟨1101749766319635368207341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23503995014818887855089941 1101749766319635368207341)
                      ·
                        rfl

theorem cell23_2145650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2145650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145650 prefixEnd_2145650 := by exact prefixLift 2145650
  have htrace : WordTrace (prefixWord ++ tailWord_2145650) baseStart_2145650 baseEnd_2145650 := by
    simpa [prefixWord, tailWord_2145650, baseEnd_2145650] using wordTrace_append hprefix tailTrace_2145650
  have hstable : (prefixWord ++ tailWord_2145650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145650).length < 2 ^ (prefixWord ++ tailWord_2145650).sum := by decide
  have hdescent : baseEnd_2145650 < baseStart_2145650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145720 : List Nat := [2, 1, 2, 1, 2, 2, 4, 9]
def baseStart_2145720 : Nat := 118140960795 + 2145720 * 2 ^ 59
def prefixEnd_2145720 : Nat := 4983230072969 + 3 ^ 40 * 2145720 * 2
def baseEnd_2145720 : Nat := 40806878146868522012297

theorem tailTrace_2145720 : CollatzResearch.WordTrace tailWord_2145720 prefixEnd_2145720 40806878146868522012297 := by
  unfold tailWord_2145720
  simp only [CollatzResearch.WordTrace]
  refine ⟨39130418893215187322877307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52173891857620249763836409 39130418893215187322877307)
  ·
    refine ⟨58695628339822780984315961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39130418893215187322877307 58695628339822780984315961)
    ·
      refine ⟨44021721254867085738236971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58695628339822780984315961 44021721254867085738236971)
      ·
        refine ⟨66032581882300628607355457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44021721254867085738236971 66032581882300628607355457)
        ·
          refine ⟨49524436411725471455516593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66032581882300628607355457 49524436411725471455516593)
          ·
            refine ⟨37143327308794103591637445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49524436411725471455516593 37143327308794103591637445)
            ·
              refine ⟨6964373870398894423432021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37143327308794103591637445 6964373870398894423432021)
              ·
                refine ⟨40806878146868522012297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6964373870398894423432021 40806878146868522012297)
                ·
                  rfl

theorem cell23_2145720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 9].length) (baseStart_2145720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145720 prefixEnd_2145720 := by exact prefixLift 2145720
  have htrace : WordTrace (prefixWord ++ tailWord_2145720) baseStart_2145720 baseEnd_2145720 := by
    simpa [prefixWord, tailWord_2145720, baseEnd_2145720] using wordTrace_append hprefix tailTrace_2145720
  have hstable : (prefixWord ++ tailWord_2145720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145720).length < 2 ^ (prefixWord ++ tailWord_2145720).sum := by decide
  have hdescent : baseEnd_2145720 < baseStart_2145720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145724 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_2145724 : Nat := 118140960795 + 2145724 * 2 ^ 59
def prefixEnd_2145724 : Nat := 4983230072969 + 3 ^ 40 * 2145724 * 2
def baseEnd_2145724 : Nat := 367262587962689359560667

theorem tailTrace_2145724 : CollatzResearch.WordTrace tailWord_2145724 prefixEnd_2145724 367262587962689359560667 := by
  unfold tailWord_2145724
  simp only [CollatzResearch.WordTrace]
  refine ⟨39130491839207941664450113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52173989118943922219266817 39130491839207941664450113)
  ·
    refine ⟨29347868879405956248337585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39130491839207941664450113 29347868879405956248337585)
    ·
      refine ⟨22010901659554467186253189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29347868879405956248337585 22010901659554467186253189)
      ·
        refine ⟨4127044061166462597422473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22010901659554467186253189 4127044061166462597422473)
        ·
          refine ⟨3095283045874846948066855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4127044061166462597422473 3095283045874846948066855)
          ·
            refine ⟨4642924568812270422100283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095283045874846948066855 4642924568812270422100283)
            ·
              refine ⟨6964386853218405633150425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4642924568812270422100283 6964386853218405633150425)
              ·
                refine ⟨5223290139913804224862819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6964386853218405633150425 5223290139913804224862819)
                ·
                  refine ⟨7834935209870706337294229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223290139913804224862819 7834935209870706337294229)
                  ·
                    refine ⟨367262587962689359560667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7834935209870706337294229 367262587962689359560667)
                    ·
                      rfl

theorem cell23_2145724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_2145724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145724 prefixEnd_2145724 := by exact prefixLift 2145724
  have htrace : WordTrace (prefixWord ++ tailWord_2145724) baseStart_2145724 baseEnd_2145724 := by
    simpa [prefixWord, tailWord_2145724, baseEnd_2145724] using wordTrace_append hprefix tailTrace_2145724
  have hstable : (prefixWord ++ tailWord_2145724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145724).length < 2 ^ (prefixWord ++ tailWord_2145724).sum := by decide
  have hdescent : baseEnd_2145724 < baseStart_2145724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145781 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2145781 : Nat := 118140960795 + 2145781 * 2 ^ 59
def prefixEnd_2145781 : Nat := 4983230072969 + 3 ^ 40 * 2145781 * 2
def baseEnd_2145781 : Nat := 1101817032285374355669239

theorem tailTrace_2145781 : CollatzResearch.WordTrace tailWord_2145781 prefixEnd_2145781 1101817032285374355669239 := by
  unfold tailWord_2145781
  simp only [CollatzResearch.WordTrace]
  refine ⟨78263062639209382063725197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52175375092806254709150131 78263062639209382063725197)
  ·
    refine ⟨29348648489703518273896949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78263062639209382063725197 29348648489703518273896949)
    ·
      refine ⟨2751435795909704838177839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29348648489703518273896949 2751435795909704838177839)
      ·
        refine ⟨4127153693864557257266759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751435795909704838177839 4127153693864557257266759)
        ·
          refine ⟨6190730540796835885900139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4127153693864557257266759 6190730540796835885900139)
          ·
            refine ⟨9286095811195253828850209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6190730540796835885900139 9286095811195253828850209)
            ·
              refine ⟨6964571858396440371637657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9286095811195253828850209 6964571858396440371637657)
              ·
                refine ⟨5223428893797330278728243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6964571858396440371637657 5223428893797330278728243)
                ·
                  refine ⟨7835143340695995418092365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5223428893797330278728243 7835143340695995418092365)
                  ·
                    refine ⟨2938178752760998281784637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7835143340695995418092365 2938178752760998281784637)
                    ·
                      refine ⟨1101817032285374355669239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2938178752760998281784637 1101817032285374355669239)
                      ·
                        rfl

theorem cell23_2145781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2145781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145781 prefixEnd_2145781 := by exact prefixLift 2145781
  have htrace : WordTrace (prefixWord ++ tailWord_2145781) baseStart_2145781 baseEnd_2145781 := by
    simpa [prefixWord, tailWord_2145781, baseEnd_2145781] using wordTrace_append hprefix tailTrace_2145781
  have hstable : (prefixWord ++ tailWord_2145781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145781).length < 2 ^ (prefixWord ++ tailWord_2145781).sum := by decide
  have hdescent : baseEnd_2145781 < baseStart_2145781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145822 : List Nat := [4, 3, 3, 1, 2, 1, 2, 7]
def baseStart_2145822 : Nat := 118140960795 + 2145822 * 2 ^ 59
def prefixEnd_2145822 : Nat := 4983230072969 + 3 ^ 40 * 2145822 * 2
def baseEnd_2145822 : Nat := 40808817962674396120613

theorem tailTrace_2145822 : CollatzResearch.WordTrace tailWord_2145822 prefixEnd_2145822 40808817962674396120613 := by
  unfold tailWord_2145822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9783069754007605758245965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52176372021373897377311813 9783069754007605758245965)
  ·
    refine ⟨3668651157752852159342237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9783069754007605758245965 3668651157752852159342237)
    ·
      refine ⟨1375744184157319559753339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3668651157752852159342237 1375744184157319559753339)
      ·
        refine ⟨2063616276235979339630009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375744184157319559753339 2063616276235979339630009)
        ·
          refine ⟨1547712207176984504722507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063616276235979339630009 1547712207176984504722507)
          ·
            refine ⟨2321568310765476757083761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547712207176984504722507 2321568310765476757083761)
            ·
              refine ⟨1741176233074107567812821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2321568310765476757083761 1741176233074107567812821)
              ·
                refine ⟨40808817962674396120613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1741176233074107567812821 40808817962674396120613)
                ·
                  rfl

theorem cell23_2145822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_2145822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145822 prefixEnd_2145822 := by exact prefixLift 2145822
  have htrace : WordTrace (prefixWord ++ tailWord_2145822) baseStart_2145822 baseEnd_2145822 := by
    simpa [prefixWord, tailWord_2145822, baseEnd_2145822] using wordTrace_append hprefix tailTrace_2145822
  have hstable : (prefixWord ++ tailWord_2145822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145822).length < 2 ^ (prefixWord ++ tailWord_2145822).sum := by decide
  have hdescent : baseEnd_2145822 < baseStart_2145822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145838 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_2145838 : Nat := 118140960795 + 2145838 * 2 ^ 59
def prefixEnd_2145838 : Nat := 4983230072969 + 3 ^ 40 * 2145838 * 2
def baseEnd_2145838 : Nat := 1101846300682680632656477

theorem tailTrace_2145838 : CollatzResearch.WordTrace tailWord_2145838 prefixEnd_2145838 1101846300682680632656477 := by
  unfold tailWord_2145838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9783142700000360099818771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52176761066668587199033445 9783142700000360099818771)
  ·
    refine ⟨14674714050000540149728157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9783142700000360099818771 14674714050000540149728157)
    ·
      refine ⟨5503017768750202556148059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14674714050000540149728157 5503017768750202556148059)
      ·
        refine ⟨8254526653125303834222089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5503017768750202556148059 8254526653125303834222089)
        ·
          refine ⟨6190894989843977875666567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8254526653125303834222089 6190894989843977875666567)
          ·
            refine ⟨9286342484765966813499851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6190894989843977875666567 9286342484765966813499851)
            ·
              refine ⟨13929513727148950220249777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9286342484765966813499851 13929513727148950220249777)
              ·
                refine ⟨10447135295361712665187333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13929513727148950220249777 10447135295361712665187333)
                ·
                  refine ⟨1958837867880321124722625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10447135295361712665187333 1958837867880321124722625)
                  ·
                    refine ⟨1469128400910240843541969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1958837867880321124722625 1469128400910240843541969)
                    ·
                      refine ⟨1101846300682680632656477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469128400910240843541969 1101846300682680632656477)
                      ·
                        rfl

theorem cell23_2145838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_2145838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145838 prefixEnd_2145838 := by exact prefixLift 2145838
  have htrace : WordTrace (prefixWord ++ tailWord_2145838) baseStart_2145838 baseEnd_2145838 := by
    simpa [prefixWord, tailWord_2145838, baseEnd_2145838] using wordTrace_append hprefix tailTrace_2145838
  have hstable : (prefixWord ++ tailWord_2145838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145838).length < 2 ^ (prefixWord ++ tailWord_2145838).sum := by decide
  have hdescent : baseEnd_2145838 < baseStart_2145838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145861 : List Nat := [1, 3, 1, 1, 1, 4, 5, 2, 5]
def baseStart_2145861 : Nat := 118140960795 + 2145861 * 2 ^ 59
def prefixEnd_2145861 : Nat := 4983230072969 + 3 ^ 40 * 2145861 * 2
def baseEnd_2145861 : Nat := 122428678970859338074319

theorem tailTrace_2145861 : CollatzResearch.WordTrace tailWord_2145861 prefixEnd_2145861 122428678970859338074319 := by
  unfold tailWord_2145861
  simp only [CollatzResearch.WordTrace]
  refine ⟨78265980478919555726637437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52177320319279703817758291 78265980478919555726637437)
  ·
    refine ⟨29349742679594833397489039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78265980478919555726637437 29349742679594833397489039)
    ·
      refine ⟨44024614019392250096233559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29349742679594833397489039 44024614019392250096233559)
      ·
        refine ⟨66036921029088375144350339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44024614019392250096233559 66036921029088375144350339)
        ·
          refine ⟨99055381543632562716525509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66036921029088375144350339 99055381543632562716525509)
          ·
            refine ⟨18572884039431105509348533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99055381543632562716525509 18572884039431105509348533)
            ·
              refine ⟨1741207878696666141501425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18572884039431105509348533 1741207878696666141501425)
              ·
                refine ⟨1305905909022499606126069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741207878696666141501425 1305905909022499606126069)
                ·
                  refine ⟨122428678970859338074319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1305905909022499606126069 122428678970859338074319)
                  ·
                    rfl

theorem cell23_2145861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_2145861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145861 prefixEnd_2145861 := by exact prefixLift 2145861
  have htrace : WordTrace (prefixWord ++ tailWord_2145861) baseStart_2145861 baseEnd_2145861 := by
    simpa [prefixWord, tailWord_2145861, baseEnd_2145861] using wordTrace_append hprefix tailTrace_2145861
  have hstable : (prefixWord ++ tailWord_2145861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145861).length < 2 ^ (prefixWord ++ tailWord_2145861).sum := by decide
  have hdescent : baseEnd_2145861 < baseStart_2145861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145907 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4]
def baseStart_2145907 : Nat := 118140960795 + 2145907 * 2 ^ 59
def prefixEnd_2145907 : Nat := 4983230072969 + 3 ^ 40 * 2145907 * 2
def baseEnd_2145907 : Nat := 1101881730847840862693659

theorem tailTrace_2145907 : CollatzResearch.WordTrace tailWord_2145907 prefixEnd_2145907 1101881730847840862693659 := by
  unfold tailWord_2145907
  simp only [CollatzResearch.WordTrace]
  refine ⟨78267658236752905582811975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52178438824501937055207983 78267658236752905582811975)
  ·
    refine ⟨117401487355129358374217963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78267658236752905582811975 117401487355129358374217963)
    ·
      refine ⟨176102231032694037561326945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117401487355129358374217963 176102231032694037561326945)
      ·
        refine ⟨132076673274520528170995209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176102231032694037561326945 132076673274520528170995209)
        ·
          refine ⟨99057504955890396128246407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132076673274520528170995209 99057504955890396128246407)
          ·
            refine ⟨148586257433835594192369611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99057504955890396128246407 148586257433835594192369611)
            ·
              refine ⟨222879386150753391288554417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148586257433835594192369611 222879386150753391288554417)
              ·
                refine ⟨167159539613065043466415813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222879386150753391288554417 167159539613065043466415813)
                ·
                  refine ⟨31342413677449695649952965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167159539613065043466415813 31342413677449695649952965)
                  ·
                    refine ⟨5876702564521817934366181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31342413677449695649952965 5876702564521817934366181)
                    ·
                      refine ⟨1101881730847840862693659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5876702564521817934366181 1101881730847840862693659)
                      ·
                        rfl

theorem cell23_2145907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_2145907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145907 prefixEnd_2145907 := by exact prefixLift 2145907
  have htrace : WordTrace (prefixWord ++ tailWord_2145907) baseStart_2145907 baseEnd_2145907 := by
    simpa [prefixWord, tailWord_2145907, baseEnd_2145907] using wordTrace_append hprefix tailTrace_2145907
  have hstable : (prefixWord ++ tailWord_2145907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145907).length < 2 ^ (prefixWord ++ tailWord_2145907).sum := by decide
  have hdescent : baseEnd_2145907 < baseStart_2145907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145914 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_2145914 : Nat := 118140960795 + 2145914 * 2 ^ 59
def prefixEnd_2145914 : Nat := 4983230072969 + 3 ^ 40 * 2145914 * 2
def baseEnd_2145914 : Nat := 1101885325212422335306127

theorem tailTrace_2145914 : CollatzResearch.WordTrace tailWord_2145914 prefixEnd_2145914 1101885325212422335306127 := by
  unfold tailWord_2145914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19566978386931886444579199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52178609031818363852211197 19566978386931886444579199)
  ·
    refine ⟨29350467580397829666868799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19566978386931886444579199 29350467580397829666868799)
    ·
      refine ⟨44025701370596744500303199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29350467580397829666868799 44025701370596744500303199)
      ·
        refine ⟨66038552055895116750454799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44025701370596744500303199 66038552055895116750454799)
        ·
          refine ⟨99057828083842675125682199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66038552055895116750454799 99057828083842675125682199)
          ·
            refine ⟨148586742125764012688523299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99057828083842675125682199 148586742125764012688523299)
            ·
              refine ⟨222880113188646019032784949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148586742125764012688523299 222880113188646019032784949)
              ·
                refine ⟨20895010611435564284323589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222880113188646019032784949 20895010611435564284323589)
                ·
                  refine ⟨3917814489644168303310673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20895010611435564284323589 3917814489644168303310673)
                  ·
                    refine ⟨2938360867233126227483005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3917814489644168303310673 2938360867233126227483005)
                    ·
                      refine ⟨1101885325212422335306127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2938360867233126227483005 1101885325212422335306127)
                      ·
                        rfl

theorem cell23_2145914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_2145914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145914 prefixEnd_2145914 := by exact prefixLift 2145914
  have htrace : WordTrace (prefixWord ++ tailWord_2145914) baseStart_2145914 baseEnd_2145914 := by
    simpa [prefixWord, tailWord_2145914, baseEnd_2145914] using wordTrace_append hprefix tailTrace_2145914
  have hstable : (prefixWord ++ tailWord_2145914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145914).length < 2 ^ (prefixWord ++ tailWord_2145914).sum := by decide
  have hdescent : baseEnd_2145914 < baseStart_2145914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145937 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2145937 : Nat := 118140960795 + 2145937 * 2 ^ 59
def prefixEnd_2145937 : Nat := 4983230072969 + 3 ^ 40 * 2145937 * 2
def baseEnd_2145937 : Nat := 1101897135267475745318521

theorem tailTrace_2145937 : CollatzResearch.WordTrace tailWord_2145937 prefixEnd_2145937 1101897135267475745318521 := by
  unfold tailWord_2145937
  simp only [CollatzResearch.WordTrace]
  refine ⟨78268752426644220706404065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52179168284429480470936043 78268752426644220706404065)
  ·
    refine ⟨58701564319983165529803049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78268752426644220706404065 58701564319983165529803049)
    ·
      refine ⟨44026173239987374147352287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58701564319983165529803049 44026173239987374147352287)
      ·
        refine ⟨66039259859981061221028431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44026173239987374147352287 66039259859981061221028431)
        ·
          refine ⟨99058889789971591831542647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66039259859981061221028431 99058889789971591831542647)
          ·
            refine ⟨148588334684957387747313971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99058889789971591831542647 148588334684957387747313971)
            ·
              refine ⟨222882502027436081620970957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148588334684957387747313971 222882502027436081620970957)
              ·
                refine ⟨83580938260288530607864109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222882502027436081620970957 83580938260288530607864109)
                ·
                  refine ⟨31342851847608198977949041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83580938260288530607864109 31342851847608198977949041)
                  ·
                    refine ⟨23507138885706149233461781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31342851847608198977949041 23507138885706149233461781)
                    ·
                      refine ⟨1101897135267475745318521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23507138885706149233461781 1101897135267475745318521)
                      ·
                        rfl

theorem cell23_2145937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2145937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145937 prefixEnd_2145937 := by exact prefixLift 2145937
  have htrace : WordTrace (prefixWord ++ tailWord_2145937) baseStart_2145937 baseEnd_2145937 := by
    simpa [prefixWord, tailWord_2145937, baseEnd_2145937] using wordTrace_append hprefix tailTrace_2145937
  have hstable : (prefixWord ++ tailWord_2145937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145937).length < 2 ^ (prefixWord ++ tailWord_2145937).sum := by decide
  have hdescent : baseEnd_2145937 < baseStart_2145937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145938 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2145938 : Nat := 118140960795 + 2145938 * 2 ^ 59
def prefixEnd_2145938 : Nat := 4983230072969 + 3 ^ 40 * 2145938 * 2
def baseEnd_2145938 : Nat := 367299216249376747135339

theorem tailTrace_2145938 : CollatzResearch.WordTrace tailWord_2145938 prefixEnd_2145938 367299216249376747135339 := by
  unfold tailWord_2145938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19567197224910149469297617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52179192599760398584793645 19567197224910149469297617)
  ·
    refine ⟨14675397918682612101973213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19567197224910149469297617 14675397918682612101973213)
    ·
      refine ⟨5503274219505979538239955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14675397918682612101973213 5503274219505979538239955)
      ·
        refine ⟨8254911329258969307359933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5503274219505979538239955 8254911329258969307359933)
        ·
          refine ⟨3095591748472113490259975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8254911329258969307359933 3095591748472113490259975)
          ·
            refine ⟨4643387622708170235389963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095591748472113490259975 4643387622708170235389963)
            ·
              refine ⟨6965081434062255353084945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4643387622708170235389963 6965081434062255353084945)
              ·
                refine ⟨5223811075546691514813709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6965081434062255353084945 5223811075546691514813709)
                ·
                  refine ⟨1958929153330009318055141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5223811075546691514813709 1958929153330009318055141)
                  ·
                    refine ⟨367299216249376747135339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958929153330009318055141 367299216249376747135339)
                    ·
                      rfl

theorem cell23_2145938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2145938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145938 prefixEnd_2145938 := by exact prefixLift 2145938
  have htrace : WordTrace (prefixWord ++ tailWord_2145938) baseStart_2145938 baseEnd_2145938 := by
    simpa [prefixWord, tailWord_2145938, baseEnd_2145938] using wordTrace_append hprefix tailTrace_2145938
  have hstable : (prefixWord ++ tailWord_2145938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145938).length < 2 ^ (prefixWord ++ tailWord_2145938).sum := by decide
  have hdescent : baseEnd_2145938 < baseStart_2145938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145971 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 4, 3, 2]
def baseStart_2145971 : Nat := 118140960795 + 2145971 * 2 ^ 59
def prefixEnd_2145971 : Nat := 4983230072969 + 3 ^ 40 * 2145971 * 2
def baseEnd_2145971 : Nat := 1101914593609728612293365

theorem tailTrace_2145971 : CollatzResearch.WordTrace tailWord_2145971 prefixEnd_2145971 1101914593609728612293365 := by
  unfold tailWord_2145971
  simp only [CollatzResearch.WordTrace]
  refine ⟨78269992508521044513141767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52179995005680696342094511 78269992508521044513141767)
  ·
    refine ⟨117404988762781566769712651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78269992508521044513141767 117404988762781566769712651)
    ·
      refine ⟨176107483144172350154568977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117404988762781566769712651 176107483144172350154568977)
      ·
        refine ⟨132080612358129262615926733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176107483144172350154568977 132080612358129262615926733)
        ·
          refine ⟨49530229634298473480972525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132080612358129262615926733 49530229634298473480972525)
          ·
            refine ⟨18573836112861927555364697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49530229634298473480972525 18573836112861927555364697)
            ·
              refine ⟨13930377084646445666523523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18573836112861927555364697 13930377084646445666523523)
              ·
                refine ⟨20895565626969668499785285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13930377084646445666523523 20895565626969668499785285)
                ·
                  refine ⟨3917918555056812843709741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20895565626969668499785285 3917918555056812843709741)
                  ·
                    refine ⟨1469219458146304816391153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3917918555056812843709741 1469219458146304816391153)
                    ·
                      refine ⟨1101914593609728612293365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469219458146304816391153 1101914593609728612293365)
                      ·
                        rfl

theorem cell23_2145971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3, 2].length) (baseStart_2145971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145971 prefixEnd_2145971 := by exact prefixLift 2145971
  have htrace : WordTrace (prefixWord ++ tailWord_2145971) baseStart_2145971 baseEnd_2145971 := by
    simpa [prefixWord, tailWord_2145971, baseEnd_2145971] using wordTrace_append hprefix tailTrace_2145971
  have hstable : (prefixWord ++ tailWord_2145971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145971).length < 2 ^ (prefixWord ++ tailWord_2145971).sum := by decide
  have hdescent : baseEnd_2145971 < baseStart_2145971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2145978 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_2145978 : Nat := 118140960795 + 2145978 * 2 ^ 59
def prefixEnd_2145978 : Nat := 4983230072969 + 3 ^ 40 * 2145978 * 2
def baseEnd_2145978 : Nat := 1101918187974310084905833

theorem tailTrace_2145978 : CollatzResearch.WordTrace tailWord_2145978 prefixEnd_2145978 1101918187974310084905833 := by
  unfold tailWord_2145978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19567561954873921177161647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52180165212997123139097725 19567561954873921177161647)
  ·
    refine ⟨29351342932310881765742471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19567561954873921177161647 29351342932310881765742471)
    ·
      refine ⟨44027014398466322648613707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29351342932310881765742471 44027014398466322648613707)
      ·
        refine ⟨66040521597699483972920561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44027014398466322648613707 66040521597699483972920561)
        ·
          refine ⟨49530391198274612979690421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66040521597699483972920561 49530391198274612979690421)
          ·
            refine ⟨4643474174838244966845977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49530391198274612979690421 4643474174838244966845977)
            ·
              refine ⟨3482605631128683725134483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4643474174838244966845977 3482605631128683725134483)
              ·
                refine ⟨5223908446693025587701725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482605631128683725134483 5223908446693025587701725)
                ·
                  refine ⟨1958965667509884595388147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5223908446693025587701725 1958965667509884595388147)
                  ·
                    refine ⟨2938448501264826893082221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1958965667509884595388147 2938448501264826893082221)
                    ·
                      refine ⟨1101918187974310084905833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2938448501264826893082221 1101918187974310084905833)
                      ·
                        rfl

theorem cell23_2145978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_2145978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2145978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2145978 prefixEnd_2145978 := by exact prefixLift 2145978
  have htrace : WordTrace (prefixWord ++ tailWord_2145978) baseStart_2145978 baseEnd_2145978 := by
    simpa [prefixWord, tailWord_2145978, baseEnd_2145978] using wordTrace_append hprefix tailTrace_2145978
  have hstable : (prefixWord ++ tailWord_2145978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2145978).length < 2 ^ (prefixWord ++ tailWord_2145978).sum := by decide
  have hdescent : baseEnd_2145978 < baseStart_2145978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2145978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146001 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_2146001 : Nat := 118140960795 + 2146001 * 2 ^ 59
def prefixEnd_2146001 : Nat := 4983230072969 + 3 ^ 40 * 2146001 * 2
def baseEnd_2146001 : Nat := 1101929998029363494918227

theorem tailTrace_2146001 : CollatzResearch.WordTrace tailWord_2146001 prefixEnd_2146001 1101929998029363494918227 := by
  unfold tailWord_2146001
  simp only [CollatzResearch.WordTrace]
  refine ⟨78271086698412359636733857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52180724465608239757822571 78271086698412359636733857)
  ·
    refine ⟨58703315023809269727550393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78271086698412359636733857 58703315023809269727550393)
    ·
      refine ⟨44027486267856952295662795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58703315023809269727550393 44027486267856952295662795)
      ·
        refine ⟨66041229401785428443494193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44027486267856952295662795 66041229401785428443494193)
        ·
          refine ⟨49530922051339071332620645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66041229401785428443494193 49530922051339071332620645)
          ·
            refine ⟨9287047884626075874866371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49530922051339071332620645 9287047884626075874866371)
            ·
              refine ⟨13930571826939113812299557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9287047884626075874866371 13930571826939113812299557)
              ·
                refine ⟨2611982217551083839806167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13930571826939113812299557 2611982217551083839806167)
                ·
                  refine ⟨3917973326326625759709251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2611982217551083839806167 3917973326326625759709251)
                  ·
                    refine ⟨5876959989489938639563877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3917973326326625759709251 5876959989489938639563877)
                    ·
                      refine ⟨1101929998029363494918227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5876959989489938639563877 1101929998029363494918227)
                      ·
                        rfl

theorem cell23_2146001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_2146001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146001 prefixEnd_2146001 := by exact prefixLift 2146001
  have htrace : WordTrace (prefixWord ++ tailWord_2146001) baseStart_2146001 baseEnd_2146001 := by
    simpa [prefixWord, tailWord_2146001, baseEnd_2146001] using wordTrace_append hprefix tailTrace_2146001
  have hstable : (prefixWord ++ tailWord_2146001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146001).length < 2 ^ (prefixWord ++ tailWord_2146001).sum := by decide
  have hdescent : baseEnd_2146001 < baseStart_2146001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146006 : List Nat := [5, 2, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2146006 : Nat := 118140960795 + 2146006 * 2 ^ 59
def prefixEnd_2146006 : Nat := 4983230072969 + 3 ^ 40 * 2146006 * 2
def baseEnd_2146006 : Nat := 367310855144211991785235

theorem tailTrace_2146006 : CollatzResearch.WordTrace tailWord_2146006 prefixEnd_2146006 367310855144211991785235 := by
  unfold tailWord_2146006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891954316462140343166617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52180846042262830327110581 4891954316462140343166617)
  ·
    refine ⟨3668965737346605257374963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4891954316462140343166617 3668965737346605257374963)
    ·
      refine ⟨5503448606019907886062445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3668965737346605257374963 5503448606019907886062445)
      ·
        refine ⟨2063793227257465457273417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5503448606019907886062445 2063793227257465457273417)
        ·
          refine ⟨1547844920443099092955063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063793227257465457273417 1547844920443099092955063)
          ·
            refine ⟨2321767380664648639432595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547844920443099092955063 2321767380664648639432595)
            ·
              refine ⟨3482651070996972959148893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2321767380664648639432595 3482651070996972959148893)
              ·
                refine ⟨1305994151623864859680835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3482651070996972959148893 1305994151623864859680835)
                ·
                  refine ⟨1958991227435797289521253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1305994151623864859680835 1958991227435797289521253)
                  ·
                    refine ⟨367310855144211991785235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1958991227435797289521253 367310855144211991785235)
                    ·
                      rfl

theorem cell23_2146006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2146006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146006 prefixEnd_2146006 := by exact prefixLift 2146006
  have htrace : WordTrace (prefixWord ++ tailWord_2146006) baseStart_2146006 baseEnd_2146006 := by
    simpa [prefixWord, tailWord_2146006, baseEnd_2146006] using wordTrace_append hprefix tailTrace_2146006
  have hstable : (prefixWord ++ tailWord_2146006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146006).length < 2 ^ (prefixWord ++ tailWord_2146006).sum := by decide
  have hdescent : baseEnd_2146006 < baseStart_2146006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146021 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2146021 : Nat := 118140960795 + 2146021 * 2 ^ 59
def prefixEnd_2146021 : Nat := 4983230072969 + 3 ^ 40 * 2146021 * 2
def baseEnd_2146021 : Nat := 1101940267642453416668135

theorem tailTrace_2146021 : CollatzResearch.WordTrace tailWord_2146021 prefixEnd_2146021 1101940267642453416668135 := by
  unfold tailWord_2146021
  simp only [CollatzResearch.WordTrace]
  refine ⟨78271816158339903052461917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52181210772226602034974611 78271816158339903052461917)
  ·
    refine ⟨29351931059377463644673219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78271816158339903052461917 29351931059377463644673219)
    ·
      refine ⟨44027896589066195467009829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29351931059377463644673219 44027896589066195467009829)
      ·
        refine ⟨8255230610449911650064343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44027896589066195467009829 8255230610449911650064343)
        ·
          refine ⟨12382845915674867475096515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8255230610449911650064343 12382845915674867475096515)
          ·
            refine ⟨18574268873512301212644773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12382845915674867475096515 18574268873512301212644773)
            ·
              refine ⟨3482675413783556477370895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18574268873512301212644773 3482675413783556477370895)
              ·
                refine ⟨5224013120675334716056343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482675413783556477370895 5224013120675334716056343)
                ·
                  refine ⟨7836019681013002074084515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5224013120675334716056343 7836019681013002074084515)
                  ·
                    refine ⟨11754029521519503111126773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7836019681013002074084515 11754029521519503111126773)
                    ·
                      refine ⟨1101940267642453416668135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11754029521519503111126773 1101940267642453416668135)
                      ·
                        rfl

theorem cell23_2146021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2146021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146021 prefixEnd_2146021 := by exact prefixLift 2146021
  have htrace : WordTrace (prefixWord ++ tailWord_2146021) baseStart_2146021 baseEnd_2146021 := by
    simpa [prefixWord, tailWord_2146021, baseEnd_2146021] using wordTrace_append hprefix tailTrace_2146021
  have hstable : (prefixWord ++ tailWord_2146021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146021).length < 2 ^ (prefixWord ++ tailWord_2146021).sum := by decide
  have hdescent : baseEnd_2146021 < baseStart_2146021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146024 : List Nat := [2, 1, 4, 1, 3, 1, 11]
def baseStart_2146024 : Nat := 118140960795 + 2146024 * 2 ^ 59
def prefixEnd_2146024 : Nat := 4983230072969 + 3 ^ 40 * 2146024 * 2
def baseEnd_2146024 : Nat := 13604219852894035863341

theorem tailTrace_2146024 : CollatzResearch.WordTrace tailWord_2146024 prefixEnd_2146024 13604219852894035863341 := by
  unfold tailWord_2146024
  simp only [CollatzResearch.WordTrace]
  refine ⟨39135962788664517282410563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52181283718219356376547417 39135962788664517282410563)
  ·
    refine ⟨58703944182996775923615845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39135962788664517282410563 58703944182996775923615845)
    ·
      refine ⟨11006989534311895485677971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58703944182996775923615845 11006989534311895485677971)
      ·
        refine ⟨16510484301467843228516957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11006989534311895485677971 16510484301467843228516957)
        ·
          refine ⟨6191431613050441210693859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16510484301467843228516957 6191431613050441210693859)
          ·
            refine ⟨9287147419575661816040789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6191431613050441210693859 9287147419575661816040789)
            ·
              refine ⟨13604219852894035863341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 9287147419575661816040789 13604219852894035863341)
              ·
                rfl

theorem cell23_2146024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 11].length) (baseStart_2146024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146024 prefixEnd_2146024 := by exact prefixLift 2146024
  have htrace : WordTrace (prefixWord ++ tailWord_2146024) baseStart_2146024 baseEnd_2146024 := by
    simpa [prefixWord, tailWord_2146024, baseEnd_2146024] using wordTrace_append hprefix tailTrace_2146024
  have hstable : (prefixWord ++ tailWord_2146024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146024).length < 2 ^ (prefixWord ++ tailWord_2146024).sum := by decide
  have hdescent : baseEnd_2146024 < baseStart_2146024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146035 : List Nat := [1, 1, 1, 2, 2, 3, 2, 6, 1, 2, 2]
def baseStart_2146035 : Nat := 118140960795 + 2146035 * 2 ^ 59
def prefixEnd_2146035 : Nat := 4983230072969 + 3 ^ 40 * 2146035 * 2
def baseEnd_2146035 : Nat := 1101947456371616361893071

theorem tailTrace_2146035 : CollatzResearch.WordTrace tailWord_2146035 prefixEnd_2146035 1101947456371616361893071 := by
  unfold tailWord_2146035
  simp only [CollatzResearch.WordTrace]
  refine ⟨78272326780289183443471559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52181551186859455628981039 78272326780289183443471559)
  ·
    refine ⟨117408490170433775165207339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78272326780289183443471559 117408490170433775165207339)
    ·
      refine ⟨176112735255650662747811009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117408490170433775165207339 176112735255650662747811009)
      ·
        refine ⟨132084551441737997060858257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176112735255650662747811009 132084551441737997060858257)
        ·
          refine ⟨99063413581303497795643693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132084551441737997060858257 99063413581303497795643693)
          ·
            refine ⟨37148780092988811673366385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99063413581303497795643693 37148780092988811673366385)
            ·
              refine ⟨27861585069741608755024789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37148780092988811673366385 27861585069741608755024789)
              ·
                refine ⟨1306011800144137910391787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27861585069741608755024789 1306011800144137910391787)
                ·
                  refine ⟨1959017700216206865587681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306011800144137910391787 1959017700216206865587681)
                  ·
                    refine ⟨1469263275162155149190761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1959017700216206865587681 1469263275162155149190761)
                    ·
                      refine ⟨1101947456371616361893071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469263275162155149190761 1101947456371616361893071)
                      ·
                        rfl

theorem cell23_2146035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 2, 2].length) (baseStart_2146035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146035 prefixEnd_2146035 := by exact prefixLift 2146035
  have htrace : WordTrace (prefixWord ++ tailWord_2146035) baseStart_2146035 baseEnd_2146035 := by
    simpa [prefixWord, tailWord_2146035, baseEnd_2146035] using wordTrace_append hprefix tailTrace_2146035
  have hstable : (prefixWord ++ tailWord_2146035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146035).length < 2 ^ (prefixWord ++ tailWord_2146035).sum := by decide
  have hdescent : baseEnd_2146035 < baseStart_2146035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146044 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2146044 : Nat := 118140960795 + 2146044 * 2 ^ 59
def prefixEnd_2146044 : Nat := 4983230072969 + 3 ^ 40 * 2146044 * 2
def baseEnd_2146044 : Nat := 1101952077697506826680529

theorem tailTrace_2146044 : CollatzResearch.WordTrace tailWord_2146044 prefixEnd_2146044 1101952077697506826680529 := by
  unfold tailWord_2146044
  simp only [CollatzResearch.WordTrace]
  refine ⟨39136327518628288990274593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52181770024837718653699457 39136327518628288990274593)
  ·
    refine ⟨29352245638971216742705945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39136327518628288990274593 29352245638971216742705945)
    ·
      refine ⟨22014184229228412557029459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29352245638971216742705945 22014184229228412557029459)
      ·
        refine ⟨33021276343842618835544189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22014184229228412557029459 33021276343842618835544189)
        ·
          refine ⟨12382978628940982063329071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33021276343842618835544189 12382978628940982063329071)
          ·
            refine ⟨18574467943411473094993607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12382978628940982063329071 18574467943411473094993607)
            ·
              refine ⟨27861701915117209642490411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18574467943411473094993607 27861701915117209642490411)
              ·
                refine ⟨41792552872675814463735617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27861701915117209642490411 41792552872675814463735617)
                ·
                  refine ⟨31344414654506860847801713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41792552872675814463735617 31344414654506860847801713)
                  ·
                    refine ⟨23508310990880145635851285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31344414654506860847801713 23508310990880145635851285)
                    ·
                      refine ⟨1101952077697506826680529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23508310990880145635851285 1101952077697506826680529)
                      ·
                        rfl

theorem cell23_2146044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2146044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146044 prefixEnd_2146044 := by exact prefixLift 2146044
  have htrace : WordTrace (prefixWord ++ tailWord_2146044) baseStart_2146044 baseEnd_2146044 := by
    simpa [prefixWord, tailWord_2146044, baseEnd_2146044] using wordTrace_append hprefix tailTrace_2146044
  have hstable : (prefixWord ++ tailWord_2146044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146044).length < 2 ^ (prefixWord ++ tailWord_2146044).sum := by decide
  have hdescent : baseEnd_2146044 < baseStart_2146044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146085 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_2146085 : Nat := 118140960795 + 2146085 * 2 ^ 59
def prefixEnd_2146085 : Nat := 4983230072969 + 3 ^ 40 * 2146085 * 2
def baseEnd_2146085 : Nat := 1101973130404341166267841

theorem tailTrace_2146085 : CollatzResearch.WordTrace tailWord_2146085 prefixEnd_2146085 1101973130404341166267841 := by
  unfold tailWord_2146085
  simp only [CollatzResearch.WordTrace]
  refine ⟨78274150430108041982791709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52182766953405361321861139 78274150430108041982791709)
  ·
    refine ⟨29352806411290515743546891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78274150430108041982791709 29352806411290515743546891)
    ·
      refine ⟨44029209616935773615320337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29352806411290515743546891 44029209616935773615320337)
      ·
        refine ⟨33021907212701830211490253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44029209616935773615320337 33021907212701830211490253)
        ·
          refine ⟨12383215204763186329308845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33021907212701830211490253 12383215204763186329308845)
          ·
            refine ⟨4643705701786194873490817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12383215204763186329308845 4643705701786194873490817)
            ·
              refine ⟨3482779276339646155118113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4643705701786194873490817 3482779276339646155118113)
              ·
                refine ⟨2612084457254734616338585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3482779276339646155118113 2612084457254734616338585)
                ·
                  refine ⟨1959063342941050962253939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612084457254734616338585 1959063342941050962253939)
                  ·
                    refine ⟨2938595014411576443380909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1959063342941050962253939 2938595014411576443380909)
                    ·
                      refine ⟨1101973130404341166267841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2938595014411576443380909 1101973130404341166267841)
                      ·
                        rfl

theorem cell23_2146085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_2146085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146085 prefixEnd_2146085 := by exact prefixLift 2146085
  have htrace : WordTrace (prefixWord ++ tailWord_2146085) baseStart_2146085 baseEnd_2146085 := by
    simpa [prefixWord, tailWord_2146085, baseEnd_2146085] using wordTrace_append hprefix tailTrace_2146085
  have hstable : (prefixWord ++ tailWord_2146085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146085).length < 2 ^ (prefixWord ++ tailWord_2146085).sum := by decide
  have hdescent : baseEnd_2146085 < baseStart_2146085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146102 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2146102 : Nat := 118140960795 + 2146102 * 2 ^ 59
def prefixEnd_2146102 : Nat := 4983230072969 + 3 ^ 40 * 2146102 * 2
def baseEnd_2146102 : Nat := 1101981859575467599755263

theorem tailTrace_2146102 : CollatzResearch.WordTrace tailWord_2146102 prefixEnd_2146102 1101981859575467599755263 := by
  unfold tailWord_2146102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4892173154440403367885035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52183180314030969257440373 4892173154440403367885035)
  ·
    refine ⟨7338259731660605051827553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4892173154440403367885035 7338259731660605051827553)
    ·
      refine ⟨5503694798745453788870665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7338259731660605051827553 5503694798745453788870665)
      ·
        refine ⟨4127771099059090341652999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5503694798745453788870665 4127771099059090341652999)
        ·
          refine ⟨6191656648588635512479499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4127771099059090341652999 6191656648588635512479499)
          ·
            refine ⟨9287484972882953268719249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6191656648588635512479499 9287484972882953268719249)
            ·
              refine ⟨6965613729662214951539437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9287484972882953268719249 6965613729662214951539437)
              ·
                refine ⟨2612105148623330606827289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6965613729662214951539437 2612105148623330606827289)
                ·
                  refine ⟨1959078861467497955120467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612105148623330606827289 1959078861467497955120467)
                  ·
                    refine ⟨2938618292201246932680701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1959078861467497955120467 2938618292201246932680701)
                    ·
                      refine ⟨1101981859575467599755263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2938618292201246932680701 1101981859575467599755263)
                      ·
                        rfl

theorem cell23_2146102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2146102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146102 prefixEnd_2146102 := by exact prefixLift 2146102
  have htrace : WordTrace (prefixWord ++ tailWord_2146102) baseStart_2146102 baseEnd_2146102 := by
    simpa [prefixWord, tailWord_2146102, baseEnd_2146102] using wordTrace_append hprefix tailTrace_2146102
  have hstable : (prefixWord ++ tailWord_2146102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146102).length < 2 ^ (prefixWord ++ tailWord_2146102).sum := by decide
  have hdescent : baseEnd_2146102 < baseStart_2146102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146108 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_2146108 : Nat := 118140960795 + 2146108 * 2 ^ 59
def prefixEnd_2146108 : Nat := 4983230072969 + 3 ^ 40 * 2146108 * 2
def baseEnd_2146108 : Nat := 1101984940459394576280235

theorem tailTrace_2146108 : CollatzResearch.WordTrace tailWord_2146108 prefixEnd_2146108 1101984940459394576280235 := by
  unfold tailWord_2146108
  simp only [CollatzResearch.WordTrace]
  refine ⟨39137494654512358455439489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52183326206016477940585985 39137494654512358455439489)
  ·
    refine ⟨29353120990884268841579617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39137494654512358455439489 29353120990884268841579617)
    ·
      refine ⟨22014840743163201631184713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29353120990884268841579617 22014840743163201631184713)
      ·
        refine ⟨16511130557372401223388535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22014840743163201631184713 16511130557372401223388535)
        ·
          refine ⟨24766695836058601835082803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16511130557372401223388535 24766695836058601835082803)
          ·
            refine ⟨37150043754087902752624205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24766695836058601835082803 37150043754087902752624205)
            ·
              refine ⟨13931266407782963532234077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37150043754087902752624205 13931266407782963532234077)
              ·
                refine ⟨5224224902918611324587779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13931266407782963532234077 5224224902918611324587779)
                ·
                  refine ⟨7836337354377916986881669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5224224902918611324587779 7836337354377916986881669)
                  ·
                    refine ⟨1469313253945859435040313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7836337354377916986881669 1469313253945859435040313)
                    ·
                      refine ⟨1101984940459394576280235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469313253945859435040313 1101984940459394576280235)
                      ·
                        rfl

theorem cell23_2146108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_2146108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146108 prefixEnd_2146108 := by exact prefixLift 2146108
  have htrace : WordTrace (prefixWord ++ tailWord_2146108) baseStart_2146108 baseEnd_2146108 := by
    simpa [prefixWord, tailWord_2146108, baseEnd_2146108] using wordTrace_append hprefix tailTrace_2146108
  have hstable : (prefixWord ++ tailWord_2146108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146108).length < 2 ^ (prefixWord ++ tailWord_2146108).sum := by decide
  have hdescent : baseEnd_2146108 < baseStart_2146108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146148 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 7]
def baseStart_2146148 : Nat := 118140960795 + 2146148 * 2 ^ 59
def prefixEnd_2146148 : Nat := 4983230072969 + 3 ^ 40 * 2146148 * 2
def baseEnd_2146148 : Nat := 122445053298397157753339

theorem tailTrace_2146148 : CollatzResearch.WordTrace tailWord_2146148 prefixEnd_2146148 122445053298397157753339 := by
  unfold tailWord_2146148
  simp only [CollatzResearch.WordTrace]
  refine ⟨39138224114439901871167549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52184298819253202494890065 39138224114439901871167549)
  ·
    refine ⟨14676834042914963201687831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39138224114439901871167549 14676834042914963201687831)
    ·
      refine ⟨22015251064372444802531747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14676834042914963201687831 22015251064372444802531747)
      ·
        refine ⟨33022876596558667203797621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22015251064372444802531747 33022876596558667203797621)
        ·
          refine ⟨3095894680927375050356027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33022876596558667203797621 3095894680927375050356027)
          ·
            refine ⟨4643842021391062575534041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3095894680927375050356027 4643842021391062575534041)
            ·
              refine ⟨3482881516043296931650531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4643842021391062575534041 3482881516043296931650531)
              ·
                refine ⟨5224322274064945397475797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3482881516043296931650531 5224322274064945397475797)
                ·
                  refine ⟨122445053298397157753339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5224322274064945397475797 122445053298397157753339)
                  ·
                    rfl

theorem cell23_2146148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_2146148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146148 prefixEnd_2146148 := by exact prefixLift 2146148
  have htrace : WordTrace (prefixWord ++ tailWord_2146148) baseStart_2146148 baseEnd_2146148 := by
    simpa [prefixWord, tailWord_2146148, baseEnd_2146148] using wordTrace_append hprefix tailTrace_2146148
  have hstable : (prefixWord ++ tailWord_2146148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146148).length < 2 ^ (prefixWord ++ tailWord_2146148).sum := by decide
  have hdescent : baseEnd_2146148 < baseStart_2146148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146181 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_2146181 : Nat := 118140960795 + 2146181 * 2 ^ 59
def prefixEnd_2146181 : Nat := 4983230072969 + 3 ^ 40 * 2146181 * 2
def baseEnd_2146181 : Nat := 1102022424547172790667399

theorem tailTrace_2146181 : CollatzResearch.WordTrace tailWord_2146181 prefixEnd_2146181 1102022424547172790667399 := by
  unfold tailWord_2146181
  simp only [CollatzResearch.WordTrace]
  refine ⟨78277651837760250378286397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52185101225173500252190931 78277651837760250378286397)
  ·
    refine ⟨29354119439160093891857399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78277651837760250378286397 29354119439160093891857399)
    ·
      refine ⟨44031179158740140837786099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29354119439160093891857399 44031179158740140837786099)
      ·
        refine ⟨66046768738110211256679149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44031179158740140837786099 66046768738110211256679149)
        ·
          refine ⟨24767538276791329221254681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66046768738110211256679149 24767538276791329221254681)
          ·
            refine ⟨18575653707593496915941011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24767538276791329221254681 18575653707593496915941011)
            ·
              refine ⟨27863480561390245373911517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18575653707593496915941011 27863480561390245373911517)
              ·
                refine ⟨10448805210521342015216819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27863480561390245373911517 10448805210521342015216819)
                ·
                  refine ⟨15673207815782013022825229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10448805210521342015216819 15673207815782013022825229)
                  ·
                    refine ⟨5877452930918254883559461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15673207815782013022825229 5877452930918254883559461)
                    ·
                      refine ⟨1102022424547172790667399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5877452930918254883559461 1102022424547172790667399)
                      ·
                        rfl

theorem cell23_2146181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_2146181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146181 prefixEnd_2146181 := by exact prefixLift 2146181
  have htrace : WordTrace (prefixWord ++ tailWord_2146181) baseStart_2146181 baseEnd_2146181 := by
    simpa [prefixWord, tailWord_2146181, baseEnd_2146181] using wordTrace_append hprefix tailTrace_2146181
  have hstable : (prefixWord ++ tailWord_2146181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146181).length < 2 ^ (prefixWord ++ tailWord_2146181).sum := by decide
  have hdescent : baseEnd_2146181 < baseStart_2146181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146288 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_2146288 : Nat := 118140960795 + 2146288 * 2 ^ 59
def prefixEnd_2146288 : Nat := 4983230072969 + 3 ^ 40 * 2146288 * 2
def baseEnd_2146288 : Nat := 1102077366977203872029407

theorem tailTrace_2146288 : CollatzResearch.WordTrace tailWord_2146288 prefixEnd_2146288 1102077366977203872029407 := by
  unfold tailWord_2146288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39140777224186303826215759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52187702965581738434954345 39140777224186303826215759)
  ·
    refine ⟨58711165836279455739323639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39140777224186303826215759 58711165836279455739323639)
    ·
      refine ⟨88066748754419183608985459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58711165836279455739323639 88066748754419183608985459)
      ·
        refine ⟨132100123131628775413478189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88066748754419183608985459 132100123131628775413478189)
        ·
          refine ⟨49537546174360790780054321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132100123131628775413478189 49537546174360790780054321)
          ·
            refine ⟨37153159630770593085040741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49537546174360790780054321 37153159630770593085040741)
            ·
              refine ⟨6966217430769486203445139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37153159630770593085040741 6966217430769486203445139)
              ·
                refine ⟨10449326146154229305167709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6966217430769486203445139 10449326146154229305167709)
                ·
                  refine ⟨3918497304807835989437891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10449326146154229305167709 3918497304807835989437891)
                  ·
                    refine ⟨5877745957211753984156837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3918497304807835989437891 5877745957211753984156837)
                    ·
                      refine ⟨1102077366977203872029407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5877745957211753984156837 1102077366977203872029407)
                      ·
                        rfl

theorem cell23_2146288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_2146288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146288 prefixEnd_2146288 := by exact prefixLift 2146288
  have htrace : WordTrace (prefixWord ++ tailWord_2146288) baseStart_2146288 baseEnd_2146288 := by
    simpa [prefixWord, tailWord_2146288, baseEnd_2146288] using wordTrace_append hprefix tailTrace_2146288
  have hstable : (prefixWord ++ tailWord_2146288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146288).length < 2 ^ (prefixWord ++ tailWord_2146288).sum := by decide
  have hdescent : baseEnd_2146288 < baseStart_2146288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146302 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2146302 : Nat := 118140960795 + 2146302 * 2 ^ 59
def prefixEnd_2146302 : Nat := 4983230072969 + 3 ^ 40 * 2146302 * 2
def baseEnd_2146302 : Nat := 367361518568788939084781

theorem tailTrace_2146302 : CollatzResearch.WordTrace tailWord_2146302 prefixEnd_2146302 367361518568788939084781 := by
  unfold tailWord_2146302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9785258133790236005430145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52188043380214592028960773 9785258133790236005430145)
  ·
    refine ⟨7338943600342677004072609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9785258133790236005430145 7338943600342677004072609)
    ·
      refine ⟨5504207700257007753054457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7338943600342677004072609 5504207700257007753054457)
      ·
        refine ⟨4128155775192755814790843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5504207700257007753054457 4128155775192755814790843)
        ·
          refine ⟨6192233662789133722186265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128155775192755814790843 6192233662789133722186265)
          ·
            refine ⟨4644175247091850291639699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6192233662789133722186265 4644175247091850291639699)
            ·
              refine ⟨6966262870637775437459549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644175247091850291639699 6966262870637775437459549)
              ·
                refine ⟨2612348576489165789047331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6966262870637775437459549 2612348576489165789047331)
                ·
                  refine ⟨3918522864733748683570997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612348576489165789047331 3918522864733748683570997)
                  ·
                    refine ⟨367361518568788939084781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3918522864733748683570997 367361518568788939084781)
                    ·
                      rfl

theorem cell23_2146302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2146302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146302 prefixEnd_2146302 := by exact prefixLift 2146302
  have htrace : WordTrace (prefixWord ++ tailWord_2146302) baseStart_2146302 baseEnd_2146302 := by
    simpa [prefixWord, tailWord_2146302, baseEnd_2146302] using wordTrace_append hprefix tailTrace_2146302
  have hstable : (prefixWord ++ tailWord_2146302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146302).length < 2 ^ (prefixWord ++ tailWord_2146302).sum := by decide
  have hdescent : baseEnd_2146302 < baseStart_2146302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146305 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2146305 : Nat := 118140960795 + 2146305 * 2 ^ 59
def prefixEnd_2146305 : Nat := 4983230072969 + 3 ^ 40 * 2146305 * 2
def baseEnd_2146305 : Nat := 1102086096148330305516829

theorem tailTrace_2146305 : CollatzResearch.WordTrace tailWord_2146305 prefixEnd_2146305 1102086096148330305516829 := by
  unfold tailWord_2146305
  simp only [CollatzResearch.WordTrace]
  refine ⟨78282174489311019555800369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52188116326207346370533579 78282174489311019555800369)
  ·
    refine ⟨58711630866983264666850277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78282174489311019555800369 58711630866983264666850277)
    ·
      refine ⟨11008430787559362125034427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58711630866983264666850277 11008430787559362125034427)
      ·
        refine ⟨16512646181339043187551641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11008430787559362125034427 16512646181339043187551641)
        ·
          refine ⟨12384484636004282390663731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16512646181339043187551641 12384484636004282390663731)
          ·
            refine ⟨18576726954006423585995597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12384484636004282390663731 18576726954006423585995597)
            ·
              refine ⟨6966272607752408844748349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18576726954006423585995597 6966272607752408844748349)
              ·
                refine ⟨2612352227907153316780631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6966272607752408844748349 2612352227907153316780631)
                ·
                  refine ⟨3918528341860729975170947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2612352227907153316780631 3918528341860729975170947)
                  ·
                    refine ⟨5877792512791094962756421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3918528341860729975170947 5877792512791094962756421)
                    ·
                      refine ⟨1102086096148330305516829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5877792512791094962756421 1102086096148330305516829)
                      ·
                        rfl

theorem cell23_2146305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2146305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146305 prefixEnd_2146305 := by exact prefixLift 2146305
  have htrace : WordTrace (prefixWord ++ tailWord_2146305) baseStart_2146305 baseEnd_2146305 := by
    simpa [prefixWord, tailWord_2146305, baseEnd_2146305] using wordTrace_append hprefix tailTrace_2146305
  have hstable : (prefixWord ++ tailWord_2146305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146305).length < 2 ^ (prefixWord ++ tailWord_2146305).sum := by decide
  have hdescent : baseEnd_2146305 < baseStart_2146305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146318 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2146318 : Nat := 118140960795 + 2146318 * 2 ^ 59
def prefixEnd_2146318 : Nat := 4983230072969 + 3 ^ 40 * 2146318 * 2
def baseEnd_2146318 : Nat := 1102092771396838754654269

theorem tailTrace_2146318 : CollatzResearch.WordTrace tailWord_2146318 prefixEnd_2146318 1102092771396838754654269 := by
  unfold tailWord_2146318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9785331079782990347002951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52188432425509281850682405 9785331079782990347002951)
  ·
    refine ⟨14677996619674485520504427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9785331079782990347002951 14677996619674485520504427)
    ·
      refine ⟨22016994929511728280756641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14677996619674485520504427 22016994929511728280756641)
      ·
        refine ⟨16512746197133796210567481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22016994929511728280756641 16512746197133796210567481)
        ·
          refine ⟨12384559647850347157925611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16512746197133796210567481 12384559647850347157925611)
          ·
            refine ⟨18576839471775520736888417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12384559647850347157925611 18576839471775520736888417)
            ·
              refine ⟨13932629603831640552666313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18576839471775520736888417 13932629603831640552666313)
              ·
                refine ⟨10449472202873730414499735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13932629603831640552666313 10449472202873730414499735)
                ·
                  refine ⟨15674208304310595621749603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10449472202873730414499735 15674208304310595621749603)
                  ·
                    refine ⟨23511312456465893432624405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15674208304310595621749603 23511312456465893432624405)
                    ·
                      refine ⟨1102092771396838754654269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23511312456465893432624405 1102092771396838754654269)
                      ·
                        rfl

theorem cell23_2146318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2146318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146318 prefixEnd_2146318 := by exact prefixLift 2146318
  have htrace : WordTrace (prefixWord ++ tailWord_2146318) baseStart_2146318 baseEnd_2146318 := by
    simpa [prefixWord, tailWord_2146318, baseEnd_2146318] using wordTrace_append hprefix tailTrace_2146318
  have hstable : (prefixWord ++ tailWord_2146318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146318).length < 2 ^ (prefixWord ++ tailWord_2146318).sum := by decide
  have hdescent : baseEnd_2146318 < baseStart_2146318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146321 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2146321 : Nat := 118140960795 + 2146321 * 2 ^ 59
def prefixEnd_2146321 : Nat := 4983230072969 + 3 ^ 40 * 2146321 * 2
def baseEnd_2146321 : Nat := 1102094311838802242916755

theorem tailTrace_2146321 : CollatzResearch.WordTrace tailWord_2146321 prefixEnd_2146321 1102094311838802242916755 := by
  unfold tailWord_2146321
  simp only [CollatzResearch.WordTrace]
  refine ⟨78282758057253054288382817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52188505371502036192255211 78282758057253054288382817)
  ·
    refine ⟨58712068542939790716287113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78282758057253054288382817 58712068542939790716287113)
    ·
      refine ⟨44034051407204843037215335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58712068542939790716287113 44034051407204843037215335)
      ·
        refine ⟨66051077110807264555823003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44034051407204843037215335 66051077110807264555823003)
        ·
          refine ⟨99076615666210896833734505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66051077110807264555823003 99076615666210896833734505)
          ·
            refine ⟨74307461749658172625300879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99076615666210896833734505 74307461749658172625300879)
            ·
              refine ⟨111461192624487258937951319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74307461749658172625300879 111461192624487258937951319)
              ·
                refine ⟨167191788936730888406926979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111461192624487258937951319 167191788936730888406926979)
                ·
                  refine ⟨250787683405096332610390469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167191788936730888406926979 250787683405096332610390469)
                  ·
                    refine ⟨47022690638455562364448213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 250787683405096332610390469 47022690638455562364448213)
                    ·
                      refine ⟨1102094311838802242916755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47022690638455562364448213 1102094311838802242916755)
                      ·
                        rfl

theorem cell23_2146321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2146321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146321 prefixEnd_2146321 := by exact prefixLift 2146321
  have htrace : WordTrace (prefixWord ++ tailWord_2146321) baseStart_2146321 baseEnd_2146321 := by
    simpa [prefixWord, tailWord_2146321, baseEnd_2146321] using wordTrace_append hprefix tailTrace_2146321
  have hstable : (prefixWord ++ tailWord_2146321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146321).length < 2 ^ (prefixWord ++ tailWord_2146321).sum := by decide
  have hdescent : baseEnd_2146321 < baseStart_2146321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146325 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_2146325 : Nat := 118140960795 + 2146325 * 2 ^ 59
def prefixEnd_2146325 : Nat := 4983230072969 + 3 ^ 40 * 2146325 * 2
def baseEnd_2146325 : Nat := 1102096365761420227266737

theorem tailTrace_2146325 : CollatzResearch.WordTrace tailWord_2146325 prefixEnd_2146325 1102096365761420227266737 := by
  unfold tailWord_2146325
  simp only [CollatzResearch.WordTrace]
  refine ⟨78282903949238562971528429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52188602632825708647685619 78282903949238562971528429)
  ·
    refine ⟨29356088980964461114323161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78282903949238562971528429 29356088980964461114323161)
    ·
      refine ⟨22017066735723345835742371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29356088980964461114323161 22017066735723345835742371)
      ·
        refine ⟨33025600103585018753613557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22017066735723345835742371 33025600103585018753613557)
        ·
          refine ⟨3096150009711095508151271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33025600103585018753613557 3096150009711095508151271)
          ·
            refine ⟨4644225014566643262226907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096150009711095508151271 4644225014566643262226907)
            ·
              refine ⟨6966337521849964893340361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644225014566643262226907 6966337521849964893340361)
              ·
                refine ⟨5224753141387473670005271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6966337521849964893340361 5224753141387473670005271)
                ·
                  refine ⟨7837129712081210505007907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5224753141387473670005271 7837129712081210505007907)
                  ·
                    refine ⟨11755694568121815757511861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7837129712081210505007907 11755694568121815757511861)
                    ·
                      refine ⟨1102096365761420227266737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11755694568121815757511861 1102096365761420227266737)
                      ·
                        rfl

theorem cell23_2146325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_2146325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146325 prefixEnd_2146325 := by exact prefixLift 2146325
  have htrace : WordTrace (prefixWord ++ tailWord_2146325) baseStart_2146325 baseEnd_2146325 := by
    simpa [prefixWord, tailWord_2146325, baseEnd_2146325] using wordTrace_append hprefix tailTrace_2146325
  have hstable : (prefixWord ++ tailWord_2146325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146325).length < 2 ^ (prefixWord ++ tailWord_2146325).sum := by decide
  have hdescent : baseEnd_2146325 < baseStart_2146325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146331 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6]
def baseStart_2146331 : Nat := 118140960795 + 2146331 * 2 ^ 59
def prefixEnd_2146331 : Nat := 4983230072969 + 3 ^ 40 * 2146331 * 2
def baseEnd_2146331 : Nat := 1102099446645347203791709

theorem tailTrace_2146331 : CollatzResearch.WordTrace tailWord_2146331 prefixEnd_2146331 1102099446645347203791709 := by
  unfold tailWord_2146331
  simp only [CollatzResearch.WordTrace]
  refine ⟨78283122787216825996246847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52188748524811217330831231 78283122787216825996246847)
  ·
    refine ⟨117424684180825238994370271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78283122787216825996246847 117424684180825238994370271)
    ·
      refine ⟨176137026271237858491555407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117424684180825238994370271 176137026271237858491555407)
      ·
        refine ⟨264205539406856787737333111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176137026271237858491555407 264205539406856787737333111)
        ·
          refine ⟨396308309110285181605999667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264205539406856787737333111 396308309110285181605999667)
          ·
            refine ⟨594462463665427772408999501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396308309110285181605999667 594462463665427772408999501)
            ·
              refine ⟨222923423874535414653374813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594462463665427772408999501 222923423874535414653374813)
              ·
                refine ⟨83596283952950780495015555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222923423874535414653374813 83596283952950780495015555)
                ·
                  refine ⟨125394425929426170742523333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83596283952950780495015555 125394425929426170742523333)
                  ·
                    refine ⟨23511454861767407014223125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125394425929426170742523333 23511454861767407014223125)
                    ·
                      refine ⟨1102099446645347203791709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23511454861767407014223125 1102099446645347203791709)
                      ·
                        rfl

theorem cell23_2146331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_2146331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146331 prefixEnd_2146331 := by exact prefixLift 2146331
  have htrace : WordTrace (prefixWord ++ tailWord_2146331) baseStart_2146331 baseEnd_2146331 := by
    simpa [prefixWord, tailWord_2146331, baseEnd_2146331] using wordTrace_append hprefix tailTrace_2146331
  have hstable : (prefixWord ++ tailWord_2146331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146331).length < 2 ^ (prefixWord ++ tailWord_2146331).sum := by decide
  have hdescent : baseEnd_2146331 < baseStart_2146331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146355 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 3]
def baseStart_2146355 : Nat := 118140960795 + 2146355 * 2 ^ 59
def prefixEnd_2146355 : Nat := 4983230072969 + 3 ^ 40 * 2146355 * 2
def baseEnd_2146355 : Nat := 1102111770181055109891599

theorem tailTrace_2146355 : CollatzResearch.WordTrace tailWord_2146355 prefixEnd_2146355 1102111770181055109891599 := by
  unfold tailWord_2146355
  simp only [CollatzResearch.WordTrace]
  refine ⟨78283998139129878095120519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52189332092753252063413679 78283998139129878095120519)
  ·
    refine ⟨117425997208694817142680779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78283998139129878095120519 117425997208694817142680779)
    ·
      refine ⟨176138995813042225714021169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117425997208694817142680779 176138995813042225714021169)
      ·
        refine ⟨132104246859781669285515877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176138995813042225714021169 132104246859781669285515877)
        ·
          refine ⟨24769546286209062991034227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132104246859781669285515877 24769546286209062991034227)
          ·
            refine ⟨37154319429313594486551341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24769546286209062991034227 37154319429313594486551341)
            ·
              refine ⟨13932869785992597932456753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37154319429313594486551341 13932869785992597932456753)
              ·
                refine ⟨10449652339494448449342565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13932869785992597932456753 10449652339494448449342565)
                ·
                  refine ⟨1959309813655209084251731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10449652339494448449342565 1959309813655209084251731)
                  ·
                    refine ⟨2938964720482813626377597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1959309813655209084251731 2938964720482813626377597)
                    ·
                      refine ⟨1102111770181055109891599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2938964720482813626377597 1102111770181055109891599)
                      ·
                        rfl

theorem cell23_2146355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 3].length) (baseStart_2146355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146355 prefixEnd_2146355 := by exact prefixLift 2146355
  have htrace : WordTrace (prefixWord ++ tailWord_2146355) baseStart_2146355 baseEnd_2146355 := by
    simpa [prefixWord, tailWord_2146355, baseEnd_2146355] using wordTrace_append hprefix tailTrace_2146355
  have hstable : (prefixWord ++ tailWord_2146355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146355).length < 2 ^ (prefixWord ++ tailWord_2146355).sum := by decide
  have hdescent : baseEnd_2146355 < baseStart_2146355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146378 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2146378 : Nat := 118140960795 + 2146378 * 2 ^ 59
def prefixEnd_2146378 : Nat := 4983230072969 + 3 ^ 40 * 2146378 * 2
def baseEnd_2146378 : Nat := 1102123580236108519903993

theorem tailTrace_2146378 : CollatzResearch.WordTrace tailWord_2146378 prefixEnd_2146378 1102123580236108519903993 := by
  unfold tailWord_2146378
  simp only [CollatzResearch.WordTrace]
  refine ⟨19571209254511638255801947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52189891345364368682138525 19571209254511638255801947)
  ·
    refine ⟨29356813881767457383702921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19571209254511638255801947 29356813881767457383702921)
    ·
      refine ⟨22017610411325593037777191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29356813881767457383702921 22017610411325593037777191)
      ·
        refine ⟨33026415616988389556665787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22017610411325593037777191 33026415616988389556665787)
        ·
          refine ⟨49539623425482584334998681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33026415616988389556665787 49539623425482584334998681)
          ·
            refine ⟨37154717569111938251249011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49539623425482584334998681 37154717569111938251249011)
            ·
              refine ⟨55732076353667907376873517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37154717569111938251249011 55732076353667907376873517)
              ·
                refine ⟨20899528632625465266327569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55732076353667907376873517 20899528632625465266327569)
                ·
                  refine ⟨15674646474469098949745677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20899528632625465266327569 15674646474469098949745677)
                  ·
                    refine ⟨5877992427925912106154629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15674646474469098949745677 5877992427925912106154629)
                    ·
                      refine ⟨1102123580236108519903993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5877992427925912106154629 1102123580236108519903993)
                      ·
                        rfl

theorem cell23_2146378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2146378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146378 prefixEnd_2146378 := by exact prefixLift 2146378
  have htrace : WordTrace (prefixWord ++ tailWord_2146378) baseStart_2146378 baseEnd_2146378 := by
    simpa [prefixWord, tailWord_2146378, baseEnd_2146378] using wordTrace_append hprefix tailTrace_2146378
  have hstable : (prefixWord ++ tailWord_2146378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146378).length < 2 ^ (prefixWord ++ tailWord_2146378).sum := by decide
  have hdescent : baseEnd_2146378 < baseStart_2146378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146388 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2146388 : Nat := 118140960795 + 2146388 * 2 ^ 59
def prefixEnd_2146388 : Nat := 4983230072969 + 3 ^ 40 * 2146388 * 2
def baseEnd_2146388 : Nat := 367376238347551160259649

theorem tailTrace_2146388 : CollatzResearch.WordTrace tailWord_2146388 prefixEnd_2146388 367376238347551160259649 := by
  unfold tailWord_2146388
  simp only [CollatzResearch.WordTrace]
  refine ⟨39142600874005162365535909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52190134498673549820714545 39142600874005162365535909)
  ·
    refine ⟨7339237663875967943537983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39142600874005162365535909 7339237663875967943537983)
    ·
      refine ⟨11008856495813951915306975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7339237663875967943537983 11008856495813951915306975)
      ·
        refine ⟨16513284743720927872960463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11008856495813951915306975 16513284743720927872960463)
        ·
          refine ⟨24769927115581391809440695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16513284743720927872960463 24769927115581391809440695)
          ·
            refine ⟨37154890673372087714161043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24769927115581391809440695 37154890673372087714161043)
            ·
              refine ⟨55732336010058131571241565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37154890673372087714161043 55732336010058131571241565)
              ·
                refine ⟨20899626003771799339215587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55732336010058131571241565 20899626003771799339215587)
                ·
                  refine ⟨31349439005657699008823381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20899626003771799339215587 31349439005657699008823381)
                  ·
                    refine ⟨367376238347551160259649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31349439005657699008823381 367376238347551160259649)
                    ·
                      rfl

theorem cell23_2146388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2146388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146388 prefixEnd_2146388 := by exact prefixLift 2146388
  have htrace : WordTrace (prefixWord ++ tailWord_2146388) baseStart_2146388 baseEnd_2146388 := by
    simpa [prefixWord, tailWord_2146388, baseEnd_2146388] using wordTrace_append hprefix tailTrace_2146388
  have hstable : (prefixWord ++ tailWord_2146388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146388).length < 2 ^ (prefixWord ++ tailWord_2146388).sum := by decide
  have hdescent : baseEnd_2146388 < baseStart_2146388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146389 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_2146389 : Nat := 118140960795 + 2146389 * 2 ^ 59
def prefixEnd_2146389 : Nat := 4983230072969 + 3 ^ 40 * 2146389 * 2
def baseEnd_2146389 : Nat := 1102129228523307976866443

theorem tailTrace_2146389 : CollatzResearch.WordTrace tailWord_2146389 prefixEnd_2146389 1102129228523307976866443 := by
  unfold tailWord_2146389
  simp only [CollatzResearch.WordTrace]
  refine ⟨78285238221006701901858221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52190158814004467934572147 78285238221006701901858221)
  ·
    refine ⟨29356964332877513213196833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78285238221006701901858221 29356964332877513213196833)
    ·
      refine ⟨22017723249658134909897625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29356964332877513213196833 22017723249658134909897625)
      ·
        refine ⟨16513292437243601182423219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22017723249658134909897625 16513292437243601182423219)
        ·
          refine ⟨24769938655865401773634829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16513292437243601182423219 24769938655865401773634829)
          ·
            refine ⟨9288726995949525665113061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24769938655865401773634829 9288726995949525665113061)
            ·
              refine ⟨1741636311740536062208699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9288726995949525665113061 1741636311740536062208699)
              ·
                refine ⟨2612454467610804093313049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1741636311740536062208699 2612454467610804093313049)
                ·
                  refine ⟨1959340850708103069984787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612454467610804093313049 1959340850708103069984787)
                  ·
                    refine ⟨2939011276062154604977181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1959340850708103069984787 2939011276062154604977181)
                    ·
                      refine ⟨1102129228523307976866443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2939011276062154604977181 1102129228523307976866443)
                      ·
                        rfl

theorem cell23_2146389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_2146389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146389 prefixEnd_2146389 := by exact prefixLift 2146389
  have htrace : WordTrace (prefixWord ++ tailWord_2146389) baseStart_2146389 baseEnd_2146389 := by
    simpa [prefixWord, tailWord_2146389, baseEnd_2146389] using wordTrace_append hprefix tailTrace_2146389
  have hstable : (prefixWord ++ tailWord_2146389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146389).length < 2 ^ (prefixWord ++ tailWord_2146389).sum := by decide
  have hdescent : baseEnd_2146389 < baseStart_2146389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146412 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 1, 4, 2]
def baseStart_2146412 : Nat := 118140960795 + 2146412 * 2 ^ 59
def prefixEnd_2146412 : Nat := 4983230072969 + 3 ^ 40 * 2146412 * 2
def baseEnd_2146412 : Nat := 1102141038578361386878837

theorem tailTrace_2146412 : CollatzResearch.WordTrace tailWord_2146412 prefixEnd_2146412 1102141038578361386878837 := by
  unfold tailWord_2146412
  simp only [CollatzResearch.WordTrace]
  refine ⟨39143038549961688414972745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52190718066615584553296993 39143038549961688414972745)
  ·
    refine ⟨29357278912471266311229559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39143038549961688414972745 29357278912471266311229559)
    ·
      refine ⟨44035918368706899466844339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29357278912471266311229559 44035918368706899466844339)
      ·
        refine ⟨66053877553060349200266509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44035918368706899466844339 66053877553060349200266509)
        ·
          refine ⟨24770204082397630950099941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66053877553060349200266509 24770204082397630950099941)
          ·
            refine ⟨4644413265449555803143739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24770204082397630950099941 4644413265449555803143739)
            ·
              refine ⟨6966619898174333704715609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644413265449555803143739 6966619898174333704715609)
              ·
                refine ⟨5224964923630750278536707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6966619898174333704715609 5224964923630750278536707)
                ·
                  refine ⟨7837447385446125417805061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5224964923630750278536707 7837447385446125417805061)
                  ·
                    refine ⟨1469521384771148515838449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7837447385446125417805061 1469521384771148515838449)
                    ·
                      refine ⟨1102141038578361386878837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469521384771148515838449 1102141038578361386878837)
                      ·
                        rfl

theorem cell23_2146412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_2146412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146412 prefixEnd_2146412 := by exact prefixLift 2146412
  have htrace : WordTrace (prefixWord ++ tailWord_2146412) baseStart_2146412 baseEnd_2146412 := by
    simpa [prefixWord, tailWord_2146412, baseEnd_2146412] using wordTrace_append hprefix tailTrace_2146412
  have hstable : (prefixWord ++ tailWord_2146412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146412).length < 2 ^ (prefixWord ++ tailWord_2146412).sum := by decide
  have hdescent : baseEnd_2146412 < baseStart_2146412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146429 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_2146429 : Nat := 118140960795 + 2146429 * 2 ^ 59
def prefixEnd_2146429 : Nat := 4983230072969 + 3 ^ 40 * 2146429 * 2
def baseEnd_2146429 : Nat := 1102149767749487820366259

theorem tailTrace_2146429 : CollatzResearch.WordTrace tailWord_2146429 prefixEnd_2146429 1102149767749487820366259 := by
  unfold tailWord_2146429
  simp only [CollatzResearch.WordTrace]
  refine ⟨78286697140861788733314341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52191131427241192488876227 78286697140861788733314341)
  ·
    refine ⟨14678755713911585387496439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78286697140861788733314341 14678755713911585387496439)
    ·
      refine ⟨22018133570867378081244659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14678755713911585387496439 22018133570867378081244659)
      ·
        refine ⟨33027200356301067121866989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22018133570867378081244659 33027200356301067121866989)
        ·
          refine ⟨12385200133612900170700121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33027200356301067121866989 12385200133612900170700121)
          ·
            refine ⟨9288900100209675128025091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12385200133612900170700121 9288900100209675128025091)
            ·
              refine ⟨13933350150314512692037637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9288900100209675128025091 13933350150314512692037637)
              ·
                refine ⟨2612503153183971129757057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13933350150314512692037637 2612503153183971129757057)
                ·
                  refine ⟨1959377364887978347317793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2612503153183971129757057 1959377364887978347317793)
                  ·
                    refine ⟨1469533023665983760488345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1959377364887978347317793 1469533023665983760488345)
                    ·
                      refine ⟨1102149767749487820366259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469533023665983760488345 1102149767749487820366259)
                      ·
                        rfl

theorem cell23_2146429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_2146429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146429 prefixEnd_2146429 := by exact prefixLift 2146429
  have htrace : WordTrace (prefixWord ++ tailWord_2146429) baseStart_2146429 baseEnd_2146429 := by
    simpa [prefixWord, tailWord_2146429, baseEnd_2146429] using wordTrace_append hprefix tailTrace_2146429
  have hstable : (prefixWord ++ tailWord_2146429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146429).length < 2 ^ (prefixWord ++ tailWord_2146429).sum := by decide
  have hdescent : baseEnd_2146429 < baseStart_2146429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146448 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 1, 7]
def baseStart_2146448 : Nat := 118140960795 + 2146448 * 2 ^ 59
def prefixEnd_2146448 : Nat := 4983230072969 + 3 ^ 40 * 2146448 * 2
def baseEnd_2146448 : Nat := 367386507960641082009557

theorem tailTrace_2146448 : CollatzResearch.WordTrace tailWord_2146448 prefixEnd_2146448 367386507960641082009557 := by
  unfold tailWord_2146448
  simp only [CollatzResearch.WordTrace]
  refine ⟨39143695063896477489127999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52191593418528636652170665 39143695063896477489127999)
  ·
    refine ⟨58715542595844716233691999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39143695063896477489127999 58715542595844716233691999)
    ·
      refine ⟨88073313893767074350537999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58715542595844716233691999 88073313893767074350537999)
      ·
        refine ⟨132109970840650611525806999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88073313893767074350537999 132109970840650611525806999)
        ·
          refine ⟨198164956260975917288710499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132109970840650611525806999 198164956260975917288710499)
          ·
            refine ⟨297247434391463875933065749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198164956260975917288710499 297247434391463875933065749)
            ·
              refine ⟨13933473487099869184362457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 297247434391463875933065749 13933473487099869184362457)
              ·
                refine ⟨10450105115324901888271843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13933473487099869184362457 10450105115324901888271843)
                ·
                  refine ⟨15675157672987352832407765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10450105115324901888271843 15675157672987352832407765)
                  ·
                    refine ⟨367386507960641082009557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15675157672987352832407765 367386507960641082009557)
                    ·
                      rfl

theorem cell23_2146448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_2146448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146448 prefixEnd_2146448 := by exact prefixLift 2146448
  have htrace : WordTrace (prefixWord ++ tailWord_2146448) baseStart_2146448 baseEnd_2146448 := by
    simpa [prefixWord, tailWord_2146448, baseEnd_2146448] using wordTrace_append hprefix tailTrace_2146448
  have hstable : (prefixWord ++ tailWord_2146448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146448).length < 2 ^ (prefixWord ++ tailWord_2146448).sum := by decide
  have hdescent : baseEnd_2146448 < baseStart_2146448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146465 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 1, 7]
def baseStart_2146465 : Nat := 118140960795 + 2146465 * 2 ^ 59
def prefixEnd_2146465 : Nat := 4983230072969 + 3 ^ 40 * 2146465 * 2
def baseEnd_2146465 : Nat := 367389417684349893172031

theorem tailTrace_2146465 : CollatzResearch.WordTrace tailWord_2146465 prefixEnd_2146465 367389417684349893172031 := by
  unfold tailWord_2146465
  simp only [CollatzResearch.WordTrace]
  refine ⟨78288010168731366881624849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52192006779154244587749899 78288010168731366881624849)
  ·
    refine ⟨58716007626548525161218637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78288010168731366881624849 58716007626548525161218637)
    ·
      refine ⟨22018502859955696935456989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58716007626548525161218637 22018502859955696935456989)
      ·
        refine ⟨8256938572483386350796371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22018502859955696935456989 8256938572483386350796371)
        ·
          refine ⟨12385407858725079526194557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8256938572483386350796371 12385407858725079526194557)
          ·
            refine ⟨4644527947021904822322959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12385407858725079526194557 4644527947021904822322959)
            ·
              refine ⟨6966791920532857233484439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4644527947021904822322959 6966791920532857233484439)
              ·
                refine ⟨10450187880799285850226659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6966791920532857233484439 10450187880799285850226659)
                ·
                  refine ⟨15675281821198928775339989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10450187880799285850226659 15675281821198928775339989)
                  ·
                    refine ⟨367389417684349893172031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15675281821198928775339989 367389417684349893172031)
                    ·
                      rfl

theorem cell23_2146465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_2146465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146465 prefixEnd_2146465 := by exact prefixLift 2146465
  have htrace : WordTrace (prefixWord ++ tailWord_2146465) baseStart_2146465 baseEnd_2146465 := by
    simpa [prefixWord, tailWord_2146465, baseEnd_2146465] using wordTrace_append hprefix tailTrace_2146465
  have hstable : (prefixWord ++ tailWord_2146465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146465).length < 2 ^ (prefixWord ++ tailWord_2146465).sum := by decide
  have hdescent : baseEnd_2146465 < baseStart_2146465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146505 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 3]
def baseStart_2146505 : Nat := 118140960795 + 2146505 * 2 ^ 59
def prefixEnd_2146505 : Nat := 4983230072969 + 3 ^ 40 * 2146505 * 2
def baseEnd_2146505 : Nat := 1102188792279229523015909

theorem tailTrace_2146505 : CollatzResearch.WordTrace tailWord_2146505 prefixEnd_2146505 1102188792279229523015909 := by
  unfold tailWord_2146505
  simp only [CollatzResearch.WordTrace]
  refine ⟨78289469088586453713080969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52192979392390969142053979 78289469088586453713080969)
  ·
    refine ⟨58717101816439840284810727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78289469088586453713080969 58717101816439840284810727)
    ·
      refine ⟨88075652724659760427216091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58717101816439840284810727 88075652724659760427216091)
      ·
        refine ⟨132113479086989640640824137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88075652724659760427216091 132113479086989640640824137)
        ·
          refine ⟨99085109315242230480618103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132113479086989640640824137 99085109315242230480618103)
          ·
            refine ⟨148627663972863345720927155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99085109315242230480618103 148627663972863345720927155)
            ·
              refine ⟨222941495959295018581390733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148627663972863345720927155 222941495959295018581390733)
              ·
                refine ⟨83603060984735631968021525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222941495959295018581390733 83603060984735631968021525)
                ·
                  refine ⟨3918893483659482748501009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83603060984735631968021525 3918893483659482748501009)
                  ·
                    refine ⟨2939170112744612061375757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3918893483659482748501009 2939170112744612061375757)
                    ·
                      refine ⟨1102188792279229523015909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2939170112744612061375757 1102188792279229523015909)
                      ·
                        rfl

theorem cell23_2146505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_2146505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146505 prefixEnd_2146505 := by exact prefixLift 2146505
  have htrace : WordTrace (prefixWord ++ tailWord_2146505) baseStart_2146505 baseEnd_2146505 := by
    simpa [prefixWord, tailWord_2146505, baseEnd_2146505] using wordTrace_append hprefix tailTrace_2146505
  have hstable : (prefixWord ++ tailWord_2146505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146505).length < 2 ^ (prefixWord ++ tailWord_2146505).sum := by decide
  have hdescent : baseEnd_2146505 < baseStart_2146505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146659 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2146659 : Nat := 118140960795 + 2146659 * 2 ^ 59
def prefixEnd_2146659 : Nat := 4983230072969 + 3 ^ 40 * 2146659 * 2
def baseEnd_2146659 : Nat := 1102267868300021920490201

theorem tailTrace_2146659 : CollatzResearch.WordTrace tailWord_2146659 prefixEnd_2146659 1102267868300021920490201 := by
  unfold tailWord_2146659
  simp only [CollatzResearch.WordTrace]
  refine ⟨78295085930028538014187031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52196723953352358676124687 78295085930028538014187031)
  ·
    refine ⟨117442628895042807021280547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78295085930028538014187031 117442628895042807021280547)
    ·
      refine ⟨176163943342564210531920821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117442628895042807021280547 176163943342564210531920821)
      ·
        refine ⟨16515369688365394737367577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176163943342564210531920821 16515369688365394737367577)
        ·
          refine ⟨12386527266274046053025683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16515369688365394737367577 12386527266274046053025683)
          ·
            refine ⟨18579790899411069079538525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12386527266274046053025683 18579790899411069079538525)
            ·
              refine ⟨6967421587279150904826947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18579790899411069079538525 6967421587279150904826947)
              ·
                refine ⟨10451132380918726357240421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6967421587279150904826947 10451132380918726357240421)
                ·
                  refine ⟨1959587321422261191982579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10451132380918726357240421 1959587321422261191982579)
                  ·
                    refine ⟨2939380982133391787973869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1959587321422261191982579 2939380982133391787973869)
                    ·
                      refine ⟨1102267868300021920490201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2939380982133391787973869 1102267868300021920490201)
                      ·
                        rfl

theorem cell23_2146659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2146659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146659 prefixEnd_2146659 := by exact prefixLift 2146659
  have htrace : WordTrace (prefixWord ++ tailWord_2146659) baseStart_2146659 baseEnd_2146659 := by
    simpa [prefixWord, tailWord_2146659, baseEnd_2146659] using wordTrace_append hprefix tailTrace_2146659
  have hstable : (prefixWord ++ tailWord_2146659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146659).length < 2 ^ (prefixWord ++ tailWord_2146659).sum := by decide
  have hdescent : baseEnd_2146659 < baseStart_2146659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146732 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_2146732 : Nat := 118140960795 + 2146732 * 2 ^ 59
def prefixEnd_2146732 : Nat := 4983230072969 + 3 ^ 40 * 2146732 * 2
def baseEnd_2146732 : Nat := 1102305352387800134877365

theorem tailTrace_2146732 : CollatzResearch.WordTrace tailWord_2146732 prefixEnd_2146732 1102305352387800134877365 := by
  unfold tailWord_2146732
  simp only [CollatzResearch.WordTrace]
  refine ⟨39148874229382035740797225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52198498972509380987729633 39148874229382035740797225)
  ·
    refine ⟨29361655672036526805597919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39148874229382035740797225 29361655672036526805597919)
    ·
      refine ⟨44042483508054790208396879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29361655672036526805597919 44042483508054790208396879)
      ·
        refine ⟨66063725262082185312595319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44042483508054790208396879 66063725262082185312595319)
        ·
          refine ⟨99095587893123277968892979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66063725262082185312595319 99095587893123277968892979)
          ·
            refine ⟨148643381839684916953339469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99095587893123277968892979 148643381839684916953339469)
            ·
              refine ⟨55741268189881843857502301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148643381839684916953339469 55741268189881843857502301)
              ·
                refine ⟨20902975571205691446563363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55741268189881843857502301 20902975571205691446563363)
                ·
                  refine ⟨31354463356808537169845045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20902975571205691446563363 31354463356808537169845045)
                  ·
                    refine ⟨2939480939700800359672973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31354463356808537169845045 2939480939700800359672973)
                    ·
                      refine ⟨1102305352387800134877365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2939480939700800359672973 1102305352387800134877365)
                      ·
                        rfl

theorem cell23_2146732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_2146732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146732 prefixEnd_2146732 := by exact prefixLift 2146732
  have htrace : WordTrace (prefixWord ++ tailWord_2146732) baseStart_2146732 baseEnd_2146732 := by
    simpa [prefixWord, tailWord_2146732, baseEnd_2146732] using wordTrace_append hprefix tailTrace_2146732
  have hstable : (prefixWord ++ tailWord_2146732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146732).length < 2 ^ (prefixWord ++ tailWord_2146732).sum := by decide
  have hdescent : baseEnd_2146732 < baseStart_2146732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146762 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2146762 : Nat := 118140960795 + 2146762 * 2 ^ 59
def prefixEnd_2146762 : Nat := 4983230072969 + 3 ^ 40 * 2146762 * 2
def baseEnd_2146762 : Nat := 1102320756807435017502227

theorem tailTrace_2146762 : CollatzResearch.WordTrace tailWord_2146762 prefixEnd_2146762 1102320756807435017502227 := by
  unfold tailWord_2146762
  simp only [CollatzResearch.WordTrace]
  refine ⟨19574710662163846651296635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52199228432436924403457693 19574710662163846651296635)
  ·
    refine ⟨29362065993245769976944953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19574710662163846651296635 29362065993245769976944953)
    ·
      refine ⟨22021549494934327482708715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29362065993245769976944953 22021549494934327482708715)
      ·
        refine ⟨33032324242401491224063073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22021549494934327482708715 33032324242401491224063073)
        ·
          refine ⟨24774243181801118418047305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33032324242401491224063073 24774243181801118418047305)
          ·
            refine ⟨18580682386350838813535479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24774243181801118418047305 18580682386350838813535479)
            ·
              refine ⟨27871023579526258220303219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18580682386350838813535479 27871023579526258220303219)
              ·
                refine ⟨41806535369289387330454829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27871023579526258220303219 41806535369289387330454829)
                ·
                  refine ⟨15677450763483520248920561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41806535369289387330454829 15677450763483520248920561)
                  ·
                    refine ⟨11758088072612640186690421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15677450763483520248920561 11758088072612640186690421)
                    ·
                      refine ⟨1102320756807435017502227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11758088072612640186690421 1102320756807435017502227)
                      ·
                        rfl

theorem cell23_2146762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2146762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146762 prefixEnd_2146762 := by exact prefixLift 2146762
  have htrace : WordTrace (prefixWord ++ tailWord_2146762) baseStart_2146762 baseEnd_2146762 := by
    simpa [prefixWord, tailWord_2146762, baseEnd_2146762] using wordTrace_append hprefix tailTrace_2146762
  have hstable : (prefixWord ++ tailWord_2146762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146762).length < 2 ^ (prefixWord ++ tailWord_2146762).sum := by decide
  have hdescent : baseEnd_2146762 < baseStart_2146762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146773 : List Nat := [1, 3, 2, 3, 1, 4, 2, 2, 5]
def baseStart_2146773 : Nat := 118140960795 + 2146773 * 2 ^ 59
def prefixEnd_2146773 : Nat := 4983230072969 + 3 ^ 40 * 2146773 * 2
def baseEnd_2146773 : Nat := 122480711677181608273853

theorem tailTrace_2146773 : CollatzResearch.WordTrace tailWord_2146773 prefixEnd_2146773 122480711677181608273853 := by
  unfold tailWord_2146773
  simp only [CollatzResearch.WordTrace]
  refine ⟨78299243851615535483836973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52199495901077023655891315 78299243851615535483836973)
  ·
    refine ⟨29362216444355825806438865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78299243851615535483836973 29362216444355825806438865)
    ·
      refine ⟨22021662333266869354829149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29362216444355825806438865 22021662333266869354829149)
      ·
        refine ⟨8258123374975076008060931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22021662333266869354829149 8258123374975076008060931)
        ·
          refine ⟨12387185062462614012091397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8258123374975076008060931 12387185062462614012091397)
          ·
            refine ⟨2322597199211740127267137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12387185062462614012091397 2322597199211740127267137)
            ·
              refine ⟨1741947899408805095450353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2322597199211740127267137 1741947899408805095450353)
              ·
                refine ⟨1306460924556603821587765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1741947899408805095450353 1306460924556603821587765)
                ·
                  refine ⟨122480711677181608273853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1306460924556603821587765 122480711677181608273853)
                  ·
                    rfl

theorem cell23_2146773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_2146773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146773 prefixEnd_2146773 := by exact prefixLift 2146773
  have htrace : WordTrace (prefixWord ++ tailWord_2146773) baseStart_2146773 baseEnd_2146773 := by
    simpa [prefixWord, tailWord_2146773, baseEnd_2146773] using wordTrace_append hprefix tailTrace_2146773
  have hstable : (prefixWord ++ tailWord_2146773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146773).length < 2 ^ (prefixWord ++ tailWord_2146773).sum := by decide
  have hdescent : baseEnd_2146773 < baseStart_2146773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146806 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_2146806 : Nat := 118140960795 + 2146806 * 2 ^ 59
def prefixEnd_2146806 : Nat := 4983230072969 + 3 ^ 40 * 2146806 * 2
def baseEnd_2146806 : Nat := 1102343349956232845352025

theorem tailTrace_2146806 : CollatzResearch.WordTrace tailWord_2146806 prefixEnd_2146806 1102343349956232845352025 := by
  unfold tailWord_2146806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893777966280998882486767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52200298306997321413192181 4893777966280998882486767)
  ·
    refine ⟨7340666949421498323730151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4893777966280998882486767 7340666949421498323730151)
    ·
      refine ⟨11011000424132247485595227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7340666949421498323730151 11011000424132247485595227)
      ·
        refine ⟨16516500636198371228392841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11011000424132247485595227 16516500636198371228392841)
        ·
          refine ⟨12387375477148778421294631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16516500636198371228392841 12387375477148778421294631)
          ·
            refine ⟨18581063215723167631941947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12387375477148778421294631 18581063215723167631941947)
            ·
              refine ⟨27871594823584751447912921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18581063215723167631941947 27871594823584751447912921)
              ·
                refine ⟨20903696117688563585934691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27871594823584751447912921 20903696117688563585934691)
                ·
                  refine ⟨31355544176532845378902037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20903696117688563585934691 31355544176532845378902037)
                  ·
                    refine ⟨1469791133274977127136033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31355544176532845378902037 1469791133274977127136033)
                    ·
                      refine ⟨1102343349956232845352025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469791133274977127136033 1102343349956232845352025)
                      ·
                        rfl

theorem cell23_2146806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_2146806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146806 prefixEnd_2146806 := by exact prefixLift 2146806
  have htrace : WordTrace (prefixWord ++ tailWord_2146806) baseStart_2146806 baseEnd_2146806 := by
    simpa [prefixWord, tailWord_2146806, baseEnd_2146806] using wordTrace_append hprefix tailTrace_2146806
  have hstable : (prefixWord ++ tailWord_2146806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146806).length < 2 ^ (prefixWord ++ tailWord_2146806).sum := by decide
  have hdescent : baseEnd_2146806 < baseStart_2146806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146812 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 8]
def baseStart_2146812 : Nat := 118140960795 + 2146812 * 2 ^ 59
def prefixEnd_2146812 : Nat := 4983230072969 + 3 ^ 40 * 2146812 * 2
def baseEnd_2146812 : Nat := 122482936760017757986333

theorem tailTrace_2146812 : CollatzResearch.WordTrace tailWord_2146812 prefixEnd_2146812 122482936760017757986333 := by
  unfold tailWord_2146812
  simp only [CollatzResearch.WordTrace]
  refine ⟨39150333149237122572253345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52200444198982830096337793 39150333149237122572253345)
  ·
    refine ⟨29362749861927841929190009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39150333149237122572253345 29362749861927841929190009)
    ·
      refine ⟨22022062396445881446892507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29362749861927841929190009 22022062396445881446892507)
      ·
        refine ⟨33033093594668822170338761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22022062396445881446892507 33033093594668822170338761)
        ·
          refine ⟨24774820196001616627754071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33033093594668822170338761 24774820196001616627754071)
          ·
            refine ⟨37162230294002424941631107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24774820196001616627754071 37162230294002424941631107)
            ·
              refine ⟨55743345441003637412446661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37162230294002424941631107 55743345441003637412446661)
              ·
                refine ⟨10451877270188182014833749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55743345441003637412446661 10451877270188182014833749)
                ·
                  refine ⟨122482936760017757986333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10451877270188182014833749 122482936760017757986333)
                  ·
                    rfl

theorem cell23_2146812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_2146812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146812 prefixEnd_2146812 := by exact prefixLift 2146812
  have htrace : WordTrace (prefixWord ++ tailWord_2146812) baseStart_2146812 baseEnd_2146812 := by
    simpa [prefixWord, tailWord_2146812, baseEnd_2146812] using wordTrace_append hprefix tailTrace_2146812
  have hstable : (prefixWord ++ tailWord_2146812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146812).length < 2 ^ (prefixWord ++ tailWord_2146812).sum := by decide
  have hdescent : baseEnd_2146812 < baseStart_2146812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146866 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_2146866 : Nat := 118140960795 + 2146866 * 2 ^ 59
def prefixEnd_2146866 : Nat := 4983230072969 + 3 ^ 40 * 2146866 * 2
def baseEnd_2146866 : Nat := 1102374158795502610601749

theorem tailTrace_2146866 : CollatzResearch.WordTrace tailWord_2146866 prefixEnd_2146866 1102374158795502610601749 := by
  unfold tailWord_2146866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19575658960069653091743113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52201757226852408244648301 19575658960069653091743113)
  ·
    refine ⟨14681744220052239818807335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19575658960069653091743113 14681744220052239818807335)
    ·
      refine ⟨22022616330078359728211003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14681744220052239818807335 22022616330078359728211003)
      ·
        refine ⟨33033924495117539592316505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22022616330078359728211003 33033924495117539592316505)
        ·
          refine ⟨24775443371338154694237379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33033924495117539592316505 24775443371338154694237379)
          ·
            refine ⟨37163165057007232041356069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24775443371338154694237379 37163165057007232041356069)
            ·
              refine ⟨6968093448188856007754263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37163165057007232041356069 6968093448188856007754263)
              ·
                refine ⟨10452140172283284011631395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968093448188856007754263 10452140172283284011631395)
                ·
                  refine ⟨15678210258424926017447093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10452140172283284011631395 15678210258424926017447093)
                  ·
                    refine ⟨1469832211727336814135665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15678210258424926017447093 1469832211727336814135665)
                    ·
                      refine ⟨1102374158795502610601749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1469832211727336814135665 1102374158795502610601749)
                      ·
                        rfl

theorem cell23_2146866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_2146866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146866 prefixEnd_2146866 := by exact prefixLift 2146866
  have htrace : WordTrace (prefixWord ++ tailWord_2146866) baseStart_2146866 baseEnd_2146866 := by
    simpa [prefixWord, tailWord_2146866, baseEnd_2146866] using wordTrace_append hprefix tailTrace_2146866
  have hstable : (prefixWord ++ tailWord_2146866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146866).length < 2 ^ (prefixWord ++ tailWord_2146866).sum := by decide
  have hdescent : baseEnd_2146866 < baseStart_2146866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146876 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_2146876 : Nat := 118140960795 + 2146876 * 2 ^ 59
def prefixEnd_2146876 : Nat := 4983230072969 + 3 ^ 40 * 2146876 * 2
def baseEnd_2146876 : Nat := 367459764534015857158901

theorem tailTrace_2146876 : CollatzResearch.WordTrace tailWord_2146876 prefixEnd_2146876 367459764534015857158901 := by
  unfold tailWord_2146876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39151500285121192037418241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52202000380161589383224321 39151500285121192037418241)
  ·
    refine ⟨29363625213840894028063681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39151500285121192037418241 29363625213840894028063681)
    ·
      refine ⟨22022718910380670521047761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29363625213840894028063681 22022718910380670521047761)
      ·
        refine ⟨16517039182785502890785821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22022718910380670521047761 16517039182785502890785821)
        ·
          refine ⟨6193889693544563584044683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16517039182785502890785821 6193889693544563584044683)
          ·
            refine ⟨9290834540316845376067025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6193889693544563584044683 9290834540316845376067025)
            ·
              refine ⟨6968125905237634032050269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9290834540316845376067025 6968125905237634032050269)
              ·
                refine ⟨2613047214464112762018851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6968125905237634032050269 2613047214464112762018851)
                ·
                  refine ⟨3919570821696169143028277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613047214464112762018851 3919570821696169143028277)
                  ·
                    refine ⟨367459764534015857158901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3919570821696169143028277 367459764534015857158901)
                    ·
                      rfl

theorem cell23_2146876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_2146876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146876 prefixEnd_2146876 := by exact prefixLift 2146876
  have htrace : WordTrace (prefixWord ++ tailWord_2146876) baseStart_2146876 baseEnd_2146876 := by
    simpa [prefixWord, tailWord_2146876, baseEnd_2146876] using wordTrace_append hprefix tailTrace_2146876
  have hstable : (prefixWord ++ tailWord_2146876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146876).length < 2 ^ (prefixWord ++ tailWord_2146876).sum := by decide
  have hdescent : baseEnd_2146876 < baseStart_2146876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146884 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2146884 : Nat := 118140960795 + 2146884 * 2 ^ 59
def prefixEnd_2146884 : Nat := 4983230072969 + 3 ^ 40 * 2146884 * 2
def baseEnd_2146884 : Nat := 367461133815761180058889

theorem tailTrace_2146884 : CollatzResearch.WordTrace tailWord_2146884 prefixEnd_2146884 367461133815761180058889 := by
  unfold tailWord_2146884
  simp only [CollatzResearch.WordTrace]
  refine ⟨39151646177106700720563853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52202194902808934294085137 39151646177106700720563853)
  ·
    refine ⟨14681867316415012770211445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39151646177106700720563853 14681867316415012770211445)
    ·
      refine ⟨1376425060913907447207323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14681867316415012770211445 1376425060913907447207323)
      ·
        refine ⟨2064637591370861170810985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376425060913907447207323 2064637591370861170810985)
        ·
          refine ⟨1548478193528145878108239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2064637591370861170810985 1548478193528145878108239)
          ·
            refine ⟨2322717290292218817162359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548478193528145878108239 2322717290292218817162359)
            ·
              refine ⟨3484075935438328225743539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322717290292218817162359 3484075935438328225743539)
              ·
                refine ⟨5226113903157492338615309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3484075935438328225743539 5226113903157492338615309)
                ·
                  refine ⟨1959792713684059626980741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5226113903157492338615309 1959792713684059626980741)
                  ·
                    refine ⟨367461133815761180058889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1959792713684059626980741 367461133815761180058889)
                    ·
                      rfl

theorem cell23_2146884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2146884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146884 prefixEnd_2146884 := by exact prefixLift 2146884
  have htrace : WordTrace (prefixWord ++ tailWord_2146884) baseStart_2146884 baseEnd_2146884 := by
    simpa [prefixWord, tailWord_2146884, baseEnd_2146884] using wordTrace_append hprefix tailTrace_2146884
  have hstable : (prefixWord ++ tailWord_2146884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146884).length < 2 ^ (prefixWord ++ tailWord_2146884).sum := by decide
  have hdescent : baseEnd_2146884 < baseStart_2146884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146913 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_2146913 : Nat := 118140960795 + 2146913 * 2 ^ 59
def prefixEnd_2146913 : Nat := 4983230072969 + 3 ^ 40 * 2146913 * 2
def baseEnd_2146913 : Nat := 1102398292386263926714033

theorem tailTrace_2146913 : CollatzResearch.WordTrace tailWord_2146913 prefixEnd_2146913 1102398292386263926714033 := by
  unfold tailWord_2146913
  simp only [CollatzResearch.WordTrace]
  refine ⟨78304350071108339393933393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52202900047405559595955595 78304350071108339393933393)
  ·
    refine ⟨58728262553331254545450045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78304350071108339393933393 58728262553331254545450045)
    ·
      refine ⟨22023098457499220454543767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58728262553331254545450045 22023098457499220454543767)
      ·
        refine ⟨33034647686248830681815651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22023098457499220454543767 33034647686248830681815651)
        ·
          refine ⟨49551971529373246022723477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33034647686248830681815651 49551971529373246022723477)
          ·
            refine ⟨2322748665439370907315163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49551971529373246022723477 2322748665439370907315163)
            ·
              refine ⟨3484122998159056360972745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322748665439370907315163 3484122998159056360972745)
              ·
                refine ⟨2613092248619292270729559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3484122998159056360972745 2613092248619292270729559)
                ·
                  refine ⟨3919638372928938406094339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613092248619292270729559 3919638372928938406094339)
                  ·
                    refine ⟨5879457559393407609141509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919638372928938406094339 5879457559393407609141509)
                    ·
                      refine ⟨1102398292386263926714033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5879457559393407609141509 1102398292386263926714033)
                      ·
                        rfl

theorem cell23_2146913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_2146913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146913 prefixEnd_2146913 := by exact prefixLift 2146913
  have htrace : WordTrace (prefixWord ++ tailWord_2146913) baseStart_2146913 baseEnd_2146913 := by
    simpa [prefixWord, tailWord_2146913, baseEnd_2146913] using wordTrace_append hprefix tailTrace_2146913
  have hstable : (prefixWord ++ tailWord_2146913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146913).length < 2 ^ (prefixWord ++ tailWord_2146913).sum := by decide
  have hdescent : baseEnd_2146913 < baseStart_2146913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146916 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_2146916 : Nat := 118140960795 + 2146916 * 2 ^ 59
def prefixEnd_2146916 : Nat := 4983230072969 + 3 ^ 40 * 2146916 * 2
def baseEnd_2146916 : Nat := 1102399832828227414976519

theorem tailTrace_2146916 : CollatzResearch.WordTrace tailWord_2146916 prefixEnd_2146916 1102399832828227414976519 := by
  unfold tailWord_2146916
  simp only [CollatzResearch.WordTrace]
  refine ⟨39152229745048735453146301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52202972993398313937528401 39152229745048735453146301)
  ·
    refine ⟨14682086154393275794929863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39152229745048735453146301 14682086154393275794929863)
    ·
      refine ⟨22023129231589913692394795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14682086154393275794929863 22023129231589913692394795)
      ·
        refine ⟨33034693847384870538592193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22023129231589913692394795 33034693847384870538592193)
        ·
          refine ⟨24776020385538652903944145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33034693847384870538592193 24776020385538652903944145)
          ·
            refine ⟨18582015289153989677958109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24776020385538652903944145 18582015289153989677958109)
            ·
              refine ⟨6968255733432746129234291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18582015289153989677958109 6968255733432746129234291)
              ·
                refine ⟨10452383600149119193851437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6968255733432746129234291 10452383600149119193851437)
                ·
                  refine ⟨3919643850055919697694289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10452383600149119193851437 3919643850055919697694289)
                  ·
                    refine ⟨2939732887541939773270717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3919643850055919697694289 2939732887541939773270717)
                    ·
                      refine ⟨1102399832828227414976519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2939732887541939773270717 1102399832828227414976519)
                      ·
                        rfl

theorem cell23_2146916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_2146916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146916 prefixEnd_2146916 := by exact prefixLift 2146916
  have htrace : WordTrace (prefixWord ++ tailWord_2146916) baseStart_2146916 baseEnd_2146916 := by
    simpa [prefixWord, tailWord_2146916, baseEnd_2146916] using wordTrace_append hprefix tailTrace_2146916
  have hstable : (prefixWord ++ tailWord_2146916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146916).length < 2 ^ (prefixWord ++ tailWord_2146916).sum := by decide
  have hdescent : baseEnd_2146916 < baseStart_2146916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146926 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2146926 : Nat := 118140960795 + 2146926 * 2 ^ 59
def prefixEnd_2146926 : Nat := 4983230072969 + 3 ^ 40 * 2146926 * 2
def baseEnd_2146926 : Nat := 1102404967634772375851473

theorem tailTrace_2146926 : CollatzResearch.WordTrace tailWord_2146926 prefixEnd_2146926 1102404967634772375851473 := by
  unfold tailWord_2146926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9788103027507655326769579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52203216146707495076104421 9788103027507655326769579)
  ·
    refine ⟨14682154541261482990154369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9788103027507655326769579 14682154541261482990154369)
    ·
      refine ⟨11011615905946112242615777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14682154541261482990154369 11011615905946112242615777)
      ·
        refine ⟨8258711929459584181961833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11011615905946112242615777 8258711929459584181961833)
        ·
          refine ⟨6194033947094688136471375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8258711929459584181961833 6194033947094688136471375)
          ·
            refine ⟨9291050920642032204707063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6194033947094688136471375 9291050920642032204707063)
            ·
              refine ⟨13936576380963048307060595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9291050920642032204707063 13936576380963048307060595)
              ·
                refine ⟨20904864571444572460590893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13936576380963048307060595 20904864571444572460590893)
                ·
                  refine ⟨7839324214291714672721585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20904864571444572460590893 7839324214291714672721585)
                  ·
                    refine ⟨5879493160718786004541189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7839324214291714672721585 5879493160718786004541189)
                    ·
                      refine ⟨1102404967634772375851473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5879493160718786004541189 1102404967634772375851473)
                      ·
                        rfl

theorem cell23_2146926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2146926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146926 prefixEnd_2146926 := by exact prefixLift 2146926
  have htrace : WordTrace (prefixWord ++ tailWord_2146926) baseStart_2146926 baseEnd_2146926 := by
    simpa [prefixWord, tailWord_2146926, baseEnd_2146926] using wordTrace_append hprefix tailTrace_2146926
  have hstable : (prefixWord ++ tailWord_2146926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146926).length < 2 ^ (prefixWord ++ tailWord_2146926).sum := by decide
  have hdescent : baseEnd_2146926 < baseStart_2146926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2146930 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_2146930 : Nat := 118140960795 + 2146930 * 2 ^ 59
def prefixEnd_2146930 : Nat := 4983230072969 + 3 ^ 40 * 2146930 * 2
def baseEnd_2146930 : Nat := 1102407021557390360201455

theorem tailTrace_2146930 : CollatzResearch.WordTrace tailWord_2146930 prefixEnd_2146930 1102407021557390360201455 := by
  unfold tailWord_2146930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19576242528011687824325561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52203313408031167531534829 19576242528011687824325561)
  ·
    refine ⟨14682181896008765868244171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19576242528011687824325561 14682181896008765868244171)
    ·
      refine ⟨22023272844013148802366257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14682181896008765868244171 22023272844013148802366257)
      ·
        refine ⟨16517454633009861601774693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22023272844013148802366257 16517454633009861601774693)
        ·
          refine ⟨3097022743689349050332755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16517454633009861601774693 3097022743689349050332755)
          ·
            refine ⟨4645534115534023575499133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097022743689349050332755 4645534115534023575499133)
            ·
              refine ⟨1742075293325258840812175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4645534115534023575499133 1742075293325258840812175)
              ·
                refine ⟨2613112939987888261218263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742075293325258840812175 2613112939987888261218263)
                ·
                  refine ⟨3919669409981832391827395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613112939987888261218263 3919669409981832391827395)
                  ·
                    refine ⟨5879504114972748587741093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3919669409981832391827395 5879504114972748587741093)
                    ·
                      refine ⟨1102407021557390360201455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5879504114972748587741093 1102407021557390360201455)
                      ·
                        rfl

theorem cell23_2146930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_2146930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2146930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2146930 prefixEnd_2146930 := by exact prefixLift 2146930
  have htrace : WordTrace (prefixWord ++ tailWord_2146930) baseStart_2146930 baseEnd_2146930 := by
    simpa [prefixWord, tailWord_2146930, baseEnd_2146930] using wordTrace_append hprefix tailTrace_2146930
  have hstable : (prefixWord ++ tailWord_2146930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2146930).length < 2 ^ (prefixWord ++ tailWord_2146930).sum := by decide
  have hdescent : baseEnd_2146930 < baseStart_2146930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2146930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
